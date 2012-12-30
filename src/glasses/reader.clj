(set! *warn-on-reflection* true)

(ns glasses.reader
  (:refer-clojure :exclude [read read-line read-string char default-data-readers])
  (:require [clojure.core :as c.c]
            [clojure.string :as s])
  (:import (clojure.lang BigInt Numbers PersistentHashMap PersistentHashSet
                         IMeta  RT Symbol Reflector Var Symbol IObj
                         PersistentVector IRecord Namespace)
           (java.util ArrayList regex.Pattern regex.Matcher)
           java.lang.reflect.Constructor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utils
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ^:private update! [what f]
  (list 'set! what (list f what)))

(defn- char [x]
  (try (clojure.core/char x)
       (catch NullPointerException e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reader protocols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Reader
  (read-char [reader] "Returns the next char from the Reader, nil if the end of stream has been reached")
  (peek-char [reader] "Returns the next char from the Reader without removing it from the reader stream"))

(defprotocol IPushbackReader
  (unread [reader ch] "Push back a single character on to the stream"))

(defprotocol IndexingReader
  (get-line-number [reader])
  (get-column-number [reader]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reader deftypes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype StringReader
    [^String s s-len ^:unsynchronized-mutable s-pos]
  Reader
  (read-char [reader]
    (when (> s-len s-pos)
      (let [r (nth s s-pos)]
        (update! s-pos inc)
        r)))
  (peek-char [reader]
    (when (> s-len s-pos)
      (nth s s-pos))))

(deftype PushbackReader
    [rdr ^objects buf buf-len ^:unsynchronized-mutable buf-pos]
  Reader
  (read-char [reader]
    (char
     (if (< buf-pos buf-len)
       (let [r (aget buf buf-pos)]
         (update! buf-pos inc)
         r)
       (read-char rdr))))
  (peek-char [reader]
    (char
     (if (< buf-pos buf-len)
       (aget buf buf-pos)
       (peek-char rdr))))
  IPushbackReader
  (unread [reader ch]
    (when ch
      (if (zero? buf-pos) (throw (RuntimeException. "Pushback buffer is full")))
      (update! buf-pos dec)
      (aset buf buf-pos ch))))

(declare newline?)

(defn- normalize-newline [rdr ch]
  (if (identical? \return ch)
    (let [c (peek-char rdr)]
      (when (identical? \formfeed c)
        (read-char rdr))
      \newline)
    ch))

(deftype IndexingPushbackReader
    [rdr ^:unsynchronized-mutable line ^:unsynchronized-mutable column
     ^:unsynchronized-mutable line-start? ^:unsynchronized-mutable prev]
  Reader
  (read-char [reader]
    (when-let [ch (read-char rdr)]
      (let [ch (normalize-newline rdr ch)]
        (set! prev line-start?)
        (set! line-start? (newline? ch))
        (when line-start?
          (set! column 0)
          (update! line inc))
        (update! column inc)
        ch)))

  (peek-char [reader]
    (peek-char rdr))

  IPushbackReader
  (unread [reader ch]
    (when line-start? (update! line dec))
    (set! line-start? prev)
    (update! column dec)
    (unread rdr ch))

  IndexingReader
  (get-line-number [reader] (inc line))
  (get-column-number [reader]  column))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; predicates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- whitespace?
  "Checks whether a given character is whitespace"
  [ch]
  (when ch
    (or (Character/isWhitespace ^Character ch)
        (identical? \, ch))))

(defn- numeric?
  "Checks whether a given character is numeric"
  [^Character ch]
  (when ch
    (Character/isDigit ch)))

(defn- comment-prefix?
  "Checks whether the character begins a comment."
  [ch]
  (identical? \; ch))

(defn- number-literal?
  "Checks whether the reader is at the start of a number literal"
  [reader initch]
  (or (numeric? initch)
      (and (or (identical? \+ initch) (identical?  \- initch))
           (numeric? (peek-char reader)))))

(defn newline? [c]
  "Checks whether the character is a newline"
  (or (identical? \newline c)
      (nil? c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; read helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare read macros dispatch-macros)

(defn reader-error
  "Throws an Exception info, if rdr is an IndexingReader, additional information about column and line number is provided"
  [rdr & msg]
  (throw (ex-info (apply str msg)
                  (merge {:type :reader-exception}
                         (if (instance? glasses.reader.IndexingReader rdr)
                           {:line (get-line-number rdr)
                            :column (get-column-number rdr)})))))

(defn macro-terminating? [ch]
  (and (not (identical? \# ch))
       (not (identical? \' ch))
       (not (identical? \: ch))
       (macros ch)))

(defn ^String read-token
  [rdr initch]
  (if-not initch
    (reader-error rdr "EOF while reading")
    (loop [sb (str initch)
           ch (peek-char rdr)]
      (if (or (nil? ch)
              (whitespace? ch)
              (macro-terminating? ch))
        sb
        (recur (str sb (read-char rdr)) (peek-char rdr))))))

(defn read-past
  "Read until first character that doesn't match pred, returning
   char."
  [pred rdr]
  (loop [ch (read-char rdr)]
    (if (pred ch)
      (recur (read-char rdr))
      ch)))

(defn skip-line
  "Advances the reader to the end of a line. Returns the reader"
  [reader _]
  (loop []
    (when-not (newline? (read-char reader))
      (recur)))
  reader)

(def ^Pattern int-pattern #"([-+]?)(?:(0)|([1-9][0-9]*)|0[xX]([0-9A-Fa-f]+)|0([0-7]+)|([1-9][0-9]?)[rR]([0-9A-Za-z]+)|0[0-9]+)(N)?")
(def ^Pattern ratio-pattern #"([-+]?[0-9]+)/([0-9]+)")
(def ^Pattern float-pattern #"([-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?)(M)?")

(defn- match-int
  [s ^Matcher m]
  (if (.group m 2)
    (if (.group m 8) 0N 0)
    (let [negate? (= "-" (.group m 1))
          a (cond
              (.group m 3) [(.group m 3) 10]
              (.group m 4) [(.group m 4) 16]
              (.group m 5) [(.group m 5) 8]
              (.group m 7) [(.group m 7) (Integer/parseInt (.group m 6))]
              :else        [nil nil])
          ^String n (a 0)
          ^int radix (a 1)]
      (when n
        (let [bn (BigInteger. n radix)
              bn (if negate? (.negate bn) bn)]
          (if (.group m 8)
            (BigInt/fromBigInteger bn)
            (if (< (.bitLength bn) 64)
              (.longValue bn)
              (BigInt/fromBigInteger bn))))))))

(defn- match-ratio
  [s ^Matcher m]
  (let [^String numerator (.group m 1)
        ^String denominator (.group m 2)]
    (/ (-> numerator   BigInteger. BigInt/fromBigInteger Numbers/reduceBigInt)
       (-> denominator BigInteger. BigInt/fromBigInteger Numbers/reduceBigInt))))

(defn- match-float
  [^String s ^Matcher m]
  (if (.group m 4)
    (BigDecimal. ^String (.group m 1))
    (Double/parseDouble s)))

(defn match-number [^String s]
  (let [s (s/replace s "_" "")]
    (cond
      (.contains s "/") (match-ratio s (doto (.matcher ratio-pattern s) .matches))

      (or (.contains s ".")
          (.contains s "M")
          (.contains s "E")
          (.contains s "e"))
      (match-float s (doto (.matcher float-pattern s) .matches))

      :else (match-int s (doto (.matcher int-pattern s) .matches)))))

(defn- parse-symbol [^String token]
  (when-not (= "" token)
    (let [ns-idx (.indexOf token "/")
          ns (if-not (== -1 ns-idx) (subs token 0 ns-idx))]
      (if (nil? ns)
        [nil token]
        (when-not (== (inc ns-idx) (count token))
          (let [sym (subs token (inc ns-idx))]
            (when (and (not (numeric? (nth sym 0)))
                       (not (= "" sym))
                       (or (= sym "/")
                           (== -1 (.indexOf sym "/"))))
              [ns sym])))))))

(declare read-tagged)

(defn read-dispatch
  [rdr _]
  (if-let [ch (read-char rdr)]
    (if-let [dm (dispatch-macros ch)]
      (dm rdr ch)
      (if-let [obj (read-tagged (doto rdr (unread ch)) ch)] ;; ctor reader is implemented as a taggged literal
        obj
        (reader-error rdr "No dispatch macro for " ch)))
    (reader-error rdr "EOF while reading character")))

(defn read-unmatched-delimiter
  [rdr ch]
  (reader-error rdr "Unmatched delimiter " ch))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; readers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def read-comment skip-line)

(defn read-unicode-char
  ([^String token offset length base]
     (let [l (+ offset length)]
       (when-not (== (count token) l)
         (throw (IllegalArgumentException. (str "Invalid unicode character: \\" token))))
       (loop [uc 0 i offset]
         (if (== i l)
           (char uc)
           (let [d (Character/digit ^char (nth token i) ^int base)]
             (if (== d -1)
               (throw (IllegalArgumentException. (str "Invalid digit: " (nth token i))))
               (recur (long (* uc (+ base d))) (inc i))))))))

  ([rdr initch base length exact?]
     (let [uc (Character/digit ^char initch ^int base)]
       (if (== uc -1)
         (throw (IllegalArgumentException. (str "Invalid digit: " initch))))
       (loop [i 1 uc uc]
         (if-not (== i length)
           (let [ch (peek-char rdr)]
             (if (or (nil? ch)
                     (whitespace? ch)
                     (macros ch))
               (if exact?
                 (throw (IllegalArgumentException.
                         (str "Invalid character length: " i ", should be: " length)))
                 (char uc))
               (let [d (Character/digit ^char ch ^int base)]
                 (read-char rdr)
                 (if (== d -1)
                   (throw (IllegalArgumentException. (str "Invalid digit: " (char ch))))
                   (recur (inc i) (long (* uc (+ base d))))))))
           (char uc))))))

(defn read-char*
  [rdr backslash]
  (let [ch (read-char rdr)]
    (if-not (nil? ch)
      (let [token (read-token rdr ch)]
        (cond

          (== 1 (count token))  (Character/valueOf (nth token 0))

          (= token "newline") \newline
          (= token "space") \space
          (= token "tab") \tab
          (= token "backspace") \backspace
          (= token "formfeed") \formfeed
          (= token "return") \return

          (.startsWith token "u")
          (let [c (read-unicode-char token 1 4 16)
                ic (int c)]
            (if (and (> ic (int \uD799))
                     (< ic (int \uE000)))
              (reader-error rdr "Invalid character constant: \\u" (Integer/toString ic 16))
              c))

          (.startsWith token "x")
          (read-unicode-char token 1 2 16)

          (.startsWith token "o")
          (let [len (dec (count token))]
            (if (> len 3)
              (reader-error rdr "Invalid octal escape sequence length: " len)
              (let [uc (read-unicode-char token 1 len 8)]
                (if (> (int uc) 0377)
                  (reader-error rdr "Octal escape sequence must be in range [0, 377]")
                  uc))))

          :else (reader-error rdr "Unsupported character: \\" token)))
      (reader-error rdr "EOF while reading character"))))

(defn ^PersistentVector read-delimited-list
  [delim rdr recursive?]
  (let [first-line  (when (instance? glasses.reader.IndexingReader rdr)
                      (get-line-number rdr))
        delim ^char delim]
    (loop [a (transient [])]
      (let [ch (read-past whitespace? rdr)]
        (when-not ch
          (reader-error rdr "EOF while reading"
                        (if first-line
                          (str ", starting at line" first-line))))
        (if (identical? delim ^char ch)
          (persistent! a)
          (if-let [macrofn (macros ch)]
            (let [mret (macrofn rdr ch)]
              (recur (if-not (= mret rdr) (conj! a mret) a)))
            (do
              (unread rdr ch)
              (let [o (read rdr true nil recursive?)]
                (recur (if-not (identical? o rdr) (conj! a o) a))))))))))

(defn read-list
  [rdr _]
  (let [[line column] (when (instance? glasses.reader.IndexingReader rdr)
                        [(get-line-number rdr) (dec (get-column-number rdr))])
        the-list (read-delimited-list \) rdr true)]
    (if (empty? the-list)
      '()
      (if-not line
        (clojure.lang.PersistentList/create the-list)
        (with-meta (clojure.lang.PersistentList/create the-list) {:line line :column column})))))

(defn read-vector
  [rdr _]
  (read-delimited-list \] rdr true))

(defn read-map
  [rdr _]
  (let [l (to-array (read-delimited-list \} rdr true))]
    (when (== 1 (bit-and (alength l) 1))
      (reader-error rdr "Map literal must contain an even number of forms"))
    (RT/map l)))

(defn read-number
  [reader initch]
  (loop [sb (str initch)
         ch (peek-char reader)]
    (if (or (nil? ch) (whitespace? ch) (macros ch))
      (or (match-number sb)
          (reader-error reader "Invalid number format [" sb "]"))
      (recur (str sb (read-char reader)) (peek-char reader)))))

(defn escape-char [sb rdr]
  (let [ch (read-char rdr)]
    (case ch
      \t "\t"
      \r "\r"
      \n "\n"
      \\ "\\"
      \" "\""
      \b "\b"
      \f "\f"
      \u (let [ch (read-char rdr)]
           (if (== -1 (Character/digit ^char ch 16))
             (reader-error rdr "Invalid unicode escape: \\u" ch)
             (read-unicode-char rdr ch 16 4 true)))
      \x (let [ch (read-char rdr)]
           (if (== -1 (Character/digit ^char ch 16))
             (reader-error rdr "Invalid unicode escape: \\x" ch)
             (read-unicode-char rdr ch 16 2 true)))
      (if (Character/isDigit ^char ch)
        (let [ch (read-unicode-char rdr ch 8 3 false)]
          (if (> (int ch) 0337)
            (reader-error rdr "Octal escape sequence must be in range [0, 377]")
            ch))
        (reader-error rdr "Unsupported escape character: \\" ch)))))

(defn read-string*
  [reader _]
  (loop [sb ""
         ch (read-char reader)]
    (case ch
      nil (reader-error reader "EOF while reading string")
      \\ (recur (str sb (escape-char sb reader)) (read-char reader))
      \" sb
      (recur (str sb ch) (read-char reader)))))

(defn read-symbol
  [rdr initch]
  (when-let [token (read-token rdr initch)]
    (case token

      ;; special symbols
      "nil" nil
      "true" true
      "false" false
      "/" '/
      "NaN" Double/NaN
      "-Infinity" Double/NEGATIVE_INFINITY
      ("Infinity" "+Infinity") Double/POSITIVE_INFINITY

      (or (when-let [p (parse-symbol token)]
            (symbol (p 0) (p 1)))
          (reader-error rdr "Invalid token: " token)))))

(defn- resolve-ns [sym]
  (or ((ns-aliases *ns*) sym)
      (find-ns sym)))

(defn read-keyword
  [reader initch]
  (let [ch (read-char reader)]
    (if-not (whitespace? ch)
      (let [token (read-token reader ch)
            s (parse-symbol token)]
        (if (and s (== -1 (.indexOf token "::")))
          (let [^String ns (s 0)
                ^String name (s 1)]
            (if (identical? \: (nth token 0))
              (if ns
                (let [ns (resolve-ns (symbol (subs ns 1)))]
                  (if ns
                    (keyword (str ns) name)
                    (reader-error reader "Invalid token: :" token)))
                (keyword (str *ns*) (subs name 1)))
              (keyword ns name)))
          (reader-error reader "Invalid token: :" token)))
      (reader-error reader "Invalid token: :"))))

(defn desugar-meta
  [f]
  (cond
    (symbol? f) {:tag (list f)}
    (keyword? f) {f true}
    :else f))

(defn wrapping-reader
  [sym]
  (fn [rdr _]
    (list sym (read rdr true nil true) nil)))

(defn throwing-reader
  [msg]
  (fn [rdr _]
    (reader-error rdr msg)))

(defn read-meta
  [rdr _]
  (let [[line column] (when (instance? glasses.reader.IndexingReader rdr)
                        [(get-line-number rdr) (dec (get-column-number rdr))])
        m (desugar-meta (read rdr true nil true))]
    (when-not (map? m)
      (reader-error rdr "Metadata must be Symbol, Keyword or Map"))
    (let [o (read rdr true nil true)]
      (if (instance? IMeta o)
        (let [m (if (and (not (nil? line))
                         (seq? o))
                  (assoc m :line line
                           :column column)
                  m)
              old-meta (meta o)
              old-tag (:tag old-meta)]
          (with-meta o (if old-tag
                         (assoc (merge old-meta (dissoc m :tag))
                           :tag (into old-tag (:tag m)))
                         (merge old-meta m))))
        (reader-error rdr "Metadata can only be applied to IMetas")))))

(defn read-set
  [rdr _]
  (PersistentHashSet/createWithCheck (read-delimited-list \} rdr true)))

;; Marker type
(deftype Tuple [coll])

(defn read-tuple
  [rdr _]
  (Tuple. (read-delimited-list \] rdr true)))

(defn read-regex
  [rdr ch]
  (loop [ch (read-char rdr) sb ""]
    (if (identical? \" ch)
      (Pattern/compile sb)
      (if (nil? ch)
        (reader-error rdr "EOF while reading regex")
        (let [ch? (when (identical? \\ ch)
                    (let [ch (read-char rdr)]
                      (when (nil? ch)
                        (reader-error rdr "EOF while reading regex"))
                      ch))]
          (recur (read-char rdr) (str sb (str ch ch?))))))))

(defn read-discard
  [rdr _]
  (read rdr true nil true)
  rdr)

(def ^:private ^:dynamic arg-env nil)

(defn- garg [n]
  (symbol (str (if (== -1 n) "rest" (str "p" n))
               "__" (RT/nextID) "#")))

(defn read-fn
  [rdr _]
  (if arg-env
    (throw (IllegalStateException. "Nested #()s are not allowed")))
  (with-bindings {#'arg-env (sorted-map)}
    (unread rdr \()
    (let [form (read rdr true nil true) ;; this sets bindings
          rargs (rseq arg-env)
          args (if rargs
                 (let [higharg (key (first rargs))]
                   (if (pos? higharg)
                     (let [args (loop [i 1 args (transient [])]
                                  (if (> i higharg)
                                    (persistent! args)
                                    (recur (inc i) (conj! args (or (get arg-env i)
                                                                   (garg i))))))
                           args (if (arg-env -1)
                                  (conj args '& (arg-env -1))
                                  args)]
                       args)))
                 [])]
      (list 'fn* args form))))

(defn register-arg [n]
  (if arg-env
    (if-let [ret (arg-env n)]
      ret
      (let [g (garg n)]
        (set! arg-env (assoc arg-env n g))
        g))))

(declare read-symbol)

(defn read-arg
  [rdr pct]
  (if-not arg-env
    (read-symbol rdr pct)
    (let [ch (peek-char rdr)]
      (if (or (not ch)
              (whitespace? ch)
              (macro-terminating? ch)) ;; we hit %
        (register-arg 1)
        (let [n (read rdr true nil true)]
          (if (= n '&)
            (register-arg -1)
            (if-not (number? n)
              (throw (IllegalStateException. "Arg literal must be %, %& or %integer"))
              (register-arg n))))))))

(def ^:private ^:dynamic gensym-env nil)

(defn read-unquote
  [rdr comma]
  (if-let [ch (peek-char rdr)]
    (if (identical? \@ ch)
      ((wrapping-reader 'clojure.core/unquote-splicing) (doto rdr read-char) \@)
      ((wrapping-reader 'clojure.core/unquote) rdr \~))))

(declare syntax-quote)
(defn unquote-splicing? [form]
  (and (seq? form)
       (= (first form) 'clojure.core/unquote-splicing)))

(defn unquote? [form]
  (and (seq? form)
       (= (first form) 'clojure.core/unquote)))

(defn- register-gensym [sym]
  (if-not gensym-env
    (throw (IllegalStateException. "Gensym literal not in syntax-quote")))
  (or (get gensym-env sym)
      (let [gs (symbol (str (subs (name sym)
                                  0 (dec (count (name sym))))
                            "__" (RT/nextID) "__auto__"))]
        (set! gensym-env (assoc gensym-env sym gs))
        gs)))

(defn- resolve-symbol [s]
  (if (pos? (.indexOf (name s) "."))
    s
    (if-let [ns-str (namespace s)]
      (let [^Namespace ns (resolve-ns (symbol ns-str))]
        (if (or (nil? ns)
                (= (name (.name ns)) ns-str)) ;; not an alias
          s
          (symbol (name (.name ns)) (name s))))
      (if-let [o ((ns-map *ns*) s)]
        (if (class? o)
          (symbol (.getName ^Class o))
          (if (var? o)
            (symbol (-> ^Var o .ns .name name) (-> ^Var o .sym name))))
        (symbol (name (.name *ns*)) (name s))))))


(defn- add-meta [form ret]
  (if (and (instance? IObj form)
           (dissoc (meta form) :line :column))
    (list 'clojure.core/with-meta ret (syntax-quote (meta form)))
    ret))

(defn syntax-quote [form]
  (->>
   (cond

     (.containsKey Compiler/specials form)
     form

     (symbol? form)
     (if (namespace form)
       (let [maybe-class ((ns-map *ns*)
                          (symbol (namespace form)))]
         (if (class? maybe-class)
           (symbol (.getName ^Class maybe-class) (name form))
           (resolve-symbol form)))
       (let [sym (name form)]
         (cond
           (.endsWith sym "#")
           (register-gensym form)

           (.startsWith sym ".")
           form

           (.startsWith sym "$") ;; == '~
           (symbol (subs sym 1))

           (.endsWith sym ".")
           (let [csym (symbol (subs sym 0 (dec (count sym))))]
             (symbol (str (name (resolve-symbol csym)) ".")))
           :else (resolve-symbol form))))

     (or (keyword? form)
         (number? form)
         (char? form)
         (string? form))
     form

     (unquote? form) form
     (unquote-splicing? form) form

     (coll? form)
     (loop [s form r (transient [])]
       (if s
         (recur (next s) (conj! r (syntax-quote (first s))))
         (seq (persistent! r))))

     :else form)

   (add-meta form)))

(defn read-syntax-quote
  [rdr backquote]
  (with-bindings {#'gensym-env {}}
    (list 'clojure.core/syntax-quote
          (syntax-quote (read rdr true nil true)))))

(defn macros [ch]
  (case ch
    \" read-string*
    \: read-keyword
    \; read-comment
    \' (wrapping-reader 'quote)
    \@ (wrapping-reader 'clojure.core/deref)
    \^ read-meta
    \` read-syntax-quote ;;(wrapping-reader 'syntax-quote)
    \~ read-unquote
    \( read-list
    \) read-unmatched-delimiter
    \[ read-vector
    \] read-unmatched-delimiter
    \{ read-map
    \} read-unmatched-delimiter
    \\ read-char*
    \% read-arg
    \# read-dispatch
    nil))

(defn dispatch-macros [ch]
  (case ch
    \' (wrapping-reader 'var)
    \( read-fn
    \{ read-set
    \[ read-tuple
    \< (throwing-reader "Unreadable form")
    \" read-regex
    \! read-comment
    \_ read-discard
    nil))

(defn read-tagged* [rdr tag f]
  (let [o (read rdr true nil true)]
    (f o)))

(defn read-ctor [rdr class-name]
  (let [class (RT/classForName (name class-name))
        ch (read-past whitespace? rdr)] ;; differs from clojure
    (if-let [[end-ch form] (case ch
                             \[ [\] :short]
                             \{ [\} :extended]
                             nil)]
      (let [entries (to-array (read-delimited-list end-ch rdr true))
            all-ctors (.getConstructors class)
            ctors-num (count all-ctors)]
        (case form
          :short
          (loop [i 0]
            (if (> i ctors-num)
              (reader-error rdr "Unexpected number of constructor arguments to " (str class)
                            ": got" (count entries))
              (if (== (count (.getParameterTypes ^Constructor (aget all-ctors i)))
                      ctors-num)
                (Reflector/invokeConstructor class entries)
                (recur (inc i)))))
          :extended
          (let [vals (RT/map entries)]
            (loop [s (keys vals)]
              (if s
                (if-not (keyword? (first s))
                  (reader-error rdr "Unreadable ctor form: key must be of type clojure.lang.Keyword")
                  (recur (next s)))))
            (Reflector/invokeStaticMethod class "create" (object-array [vals])))))
      (reader-error rdr "Invalid reader constructor form"))))

(declare default-data-readers)

(defn read-tagged [rdr initch]
  (let [tag (read rdr true nil false)]
    (if-not (symbol? tag)
      (reader-error rdr "Reader tag must be a symbol"))
    (if-let [f (or (*data-readers* tag)
                   (default-data-readers tag))]
      (read-tagged* rdr tag f)
      (if (.contains (name tag) ".")
        (read-ctor rdr tag)
        (reader-error rdr "No reader function for tag " (name tag))))))

;; marker type
(deftype complex [real imaginary])

(defn complex-reader [form]
  {:pre [(vector? form)
         (= 2 (count form))
         (every? #(or (number? %)
                      (instance? complex %)) form)]}
  (->complex (first form) (second form)))

(defmethod print-method complex [^complex c ^java.io.Writer w]
  (.write w (str "#c [" (.real c) " " (.imaginary c) "]")))

;; marker type
(deftype bitmap [elements])

(defn bitmap-reader [form]
  {:pre [(vector? form)
         (every? #{0 1} form)]}
  (->bitmap form))

(defmethod print-method bitmap [^bitmap b ^java.io.Writer w]
  (.write w (str "#bitmap " (.elements b))))

(def default-data-readers
  (assoc c.c/default-data-readers
    'c #'complex-reader
    'bitmap #'bitmap-reader))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Public API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn string-reader
  "Creates a StringReader from a given string"
  ([^String s]
     (StringReader. s (count s) 0)))

(defn string-push-back-reader
  "Creates a PushbackReader from a given string"
  ([s]
     (string-push-back-reader s 1))
  ([^String s buf-len]
     (PushbackReader. (string-reader s) (object-array buf-len) buf-len buf-len)))

(defn indexing-push-back-reader
  "Creates an IndexingPushbackReader from a given string or Reader"
  ([s-or-rdr]
     (IndexingPushbackReader.
      (string-push-back-reader s-or-rdr) 0 1 true nil))
  ([s-or-rdr buf-len]
     (IndexingPushbackReader.
      (string-push-back-reader s-or-rdr buf-len) 0 1 true nil)))

(defn read
  "Reads the first object from an IPushbackReader or a java.io.PushbackReader.
Returns the object read. If EOF, throws if eof-error? is true. Otherwise returns sentinel."
  ([] (read *in*))
  ([reader] (read reader true nil))
  ([reader eof-error? sentinel] (read reader eof-error? sentinel false))
  ([^glasses.reader.IPushbackReader reader eof-error? sentinel recursive?]
     (try
       (let [ch (read-char reader)]
         (cond
           (whitespace? ch) (read reader eof-error? sentinel recursive?)
           (nil? ch) (if eof-error? (reader-error reader "EOF") sentinel)
           (number-literal? reader ch) (read-number reader ch)
           (comment-prefix? ch) (read (read-comment reader ch) eof-error? sentinel recursive?)
           :else (let [f (macros ch)]
                   (if f
                     (let [res (f reader ch)]
                       (if (identical? res reader)
                         (read reader eof-error? sentinel recursive?)
                         res))
                     (read-symbol reader ch)))))
        (catch Exception e
          (if (instance? clojure.lang.ExceptionInfo e)
            (throw e)
            (throw (ex-info (.getMessage e)
                            (merge {:type :reader-exception}
                                   (if (instance? glasses.reader.IndexingReader reader)
                                     {:line (get-line-number reader)
                                      :column (get-column-number reader)}))
                            e)))))))

(defn read-string
  "Reads one object from the string s"
  [s]
  (read (string-push-back-reader s) true nil false))

(defn read-line
  "Reads a line from the reader or from *in* if no reader is specified"
  ([] (read-line *in*))
  ([rdr]
     (loop [c (read-char rdr) s ""]
       (if (newline? c)
         s
         (recur (read-char rdr) (str s c))))))
