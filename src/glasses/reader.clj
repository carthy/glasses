(set! *warn-on-reflection* true)

(ns glasses.reader
  (:refer-clojure :exclude [read read-line read-string char default-data-readers])
  (:require [clojure.core :as c.c]
            [clojure.string :as s]
            [glasses.reader-types :refer :all]
            [glasses.utils :refer :all])
  (:import (clojure.lang PersistentHashSet IMeta
                         RT Symbol Reflector Var IObj
                         PersistentVector IRecord Namespace
                         PersistentQueue)
           (clojure.lang BigInt Numbers)
           (java.util regex.Pattern regex.Matcher)
           java.lang.reflect.Constructor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; read helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn number-literal?
  "Checks whether the reader is at the start of a number literal"
  [reader initch]
  (or (numeric? initch)
      (and (or (identical? \+ initch) (identical?  \- initch))
           (numeric? (peek-char reader)))))

(declare read macros dispatch-macros)

(defn macro-terminating? [ch]
  (and (not (identical? \# ch))
       (not (identical? \' ch))
       (not (identical? \: ch))
       (not (identical? \% ch))
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

(def ^Pattern int-pattern #"([-+]?)(?:(0)|([1-9][0-9]*)|0[xX]([0-9A-Fa-f]+)|0([0-7]+)|([1-9][0-9]?)[rR]([0-9A-Za-z]+)|0[0-9]+)")
(def ^Pattern ratio-pattern #"([-+]?[0-9]+)/([0-9]+)")
(def ^Pattern float-pattern #"([-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?)((?:p)([0-9]+))?")

(defn- match-int
  [s ^Matcher m]
  (if (.group m 2)
    0
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
          (if (< (.bitLength bn) 64)
            (.longValue bn)
            (BigInt/fromBigInteger bn)))))))

(defn- match-ratio
  [s ^Matcher m]
  (let [^String numerator (.group m 1)
        ^String denominator (.group m 2)]
    (/ (-> numerator   BigInteger. BigInt/fromBigInteger Numbers/reduceBigInt)
       (-> denominator BigInteger. BigInt/fromBigInteger Numbers/reduceBigInt))))

(deftype DoubleWithPrecision [double precision])
(defn- match-float
  [^String s ^Matcher m]
  (let [d (Double/parseDouble (.group m 1))]
    (if-let [precision (.group m 5)]
      (DoubleWithPrecision. d (Integer/parseInt precision))
      d)))

(defn match-number [^String s]
  (let [s (s/replace s "_" "")]

(defn match-number [^String s]
  (let [int-matcher (.matcher int-pattern s)]
    (if (.matches int-matcher)
      (match-int int-matcher)
      (let [float-matcher (.matcher float-pattern s)]
        (if (.matches float-matcher)
          (match-float s float-matcher)
          (let [ratio-matcher (.matcher ratio-pattern s)]
            (when (.matches ratio-matcher)
              (match-ratio ratio-matcher))))))))))

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
       (loop [i offset uc 0]
         (if (== i l)
           (char uc)
           (let [d (Character/digit ^char (nth token i) ^int base)]
             (if (== d -1)
               (throw (IllegalArgumentException. (str "Invalid digit: " (nth token i))))
               (recur (inc i) (long (+ d (* uc base))))))))))

  ([rdr initch base length exact?]
     (loop [i 1 uc (Character/digit ^char initch ^int base)]
       (if (== uc -1)
         (throw (IllegalArgumentException. (str "Invalid digit: " initch)))
         (if-not (== i length)
           (let [ch (peek-char rdr)]
             (if (or (whitespace? ch)
                     (macros ch)
                     (nil? ch))
               (if exact?
                 (throw (IllegalArgumentException.
                         (str "Invalid character length: " i ", should be: " length)))
                 (char uc))
               (let [d (Character/digit ^char ch ^int base)]
                 (read-char rdr)
                 (if (== d -1)
                   (throw (IllegalArgumentException. (str "Invalid digit: " ch)))
                   (recur (inc i) (long (+ d (* uc base))))))))
           (char uc))))))

(let [upper-limit (int \uD7ff)
      lower-limit (int \uE000)]
  (defn read-char*
    [rdr backslash]
    (let [ch (read-char rdr)]
      (if-not (nil? ch)
        (let [token (read-token rdr ch)
              token-len (count token)]
          (cond

           (== 1 token-len)  (Character/valueOf (nth token 0))

           (= token "newline") \newline
           (= token "space") \space
           (= token "tab") \tab
           (= token "backspace") \backspace
           (= token "formfeed") \formfeed
           (= token "return") \return

           (.startsWith token "u")
           (let [c (read-unicode-char token 1 4 16)
                 ic (int c)]
             (if (and (> ic upper-limit)
                      (< ic lower-limit))
               (reader-error rdr "Invalid character constant: \\u" (Integer/toString ic 16))
               c))

           (.startsWith token "x")
           (read-unicode-char token 1 2 16)

           (.startsWith token "o")
           (let [len (dec token-len)]
             (if (> len 3)
               (reader-error rdr "Invalid octal escape sequence length: " len)
               (let [uc (read-unicode-char token 1 len 8)]
                 (if (> (int uc) 0377)
                   (reader-error rdr "Octal escape sequence must be in range [0, 377]")
                   uc))))

           :else (reader-error rdr "Unsupported character: \\" token)))
        (reader-error rdr "EOF while reading character")))))

(defn ^PersistentVector read-delimited
  [delim rdr recursive?]
  (let [first-line  (when (indexing-reader? rdr)
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
  (let [[line column] (when (indexing-reader? rdr)
                        [(get-line-number rdr) (dec (get-column-number rdr))])
        the-list (read-delimited \) rdr true)]
    (if (empty? the-list)
      '()
      (with-meta (clojure.lang.PersistentList/create the-list)
        (when line
          {:line line :column column})))))

(defn read-vector
  [rdr _]
  (let [[line column] (when (indexing-reader? rdr)
                        [(get-line-number rdr) (dec (get-column-number rdr))])
        the-vector (read-delimited \] rdr true)]
    (with-meta the-vector
      (when line
        {:line line :column column}))))

(defn read-map
  [rdr _]
  (let [[line column] (when (indexing-reader? rdr)
                        [(get-line-number rdr) (dec (get-column-number rdr))])
        l (to-array (read-delimited \} rdr true))]
    (when (== 1 (bit-and (alength l) 1))
      (reader-error rdr "Map literal must contain an even number of forms"))
    (with-meta (RT/map l)
      (when line
        {:line line :column column}))))

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
    (let [[line column] (when (indexing-reader? rdr)
                          [(get-line-number rdr) (dec (get-column-number rdr))])]
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
              (when-not (and (p 0)
                             (.startsWith ^String (p 1) "."))
                (with-meta (symbol (p 0) (p 1))
                  (when line
                    {:line line :column column}))))
            (reader-error rdr "Invalid token: " token))))))

(defn read-keyword
  [reader initch]
  (let [ch (read-char reader)]
    (if-not (whitespace? ch)
      (let [token (read-token reader ch)
            s (parse-symbol token)]
        (if (and s (== -1 (.indexOf token "::")))
          (let [^String ns (s 0)
                ^String name (s 1)]
            (if (or (identical? \: (nth ns 0))
                    (identical? \: (nth name 0)))
              (reader-error reader "Invalid token: :" token)
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
  (let [[line column] (when (indexing-reader? rdr)
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
  (PersistentHashSet/createWithCheck (read-delimited \} rdr true)))

;; Marker type
(deftype Tuple [coll])

(defn read-tuple
  [rdr _]
  (Tuple. (read-delimited \] rdr true)))

(defmethod print-method Tuple [^Tuple t ^java.io.Writer w]
  (.write w (str "#" (.coll t))))
(defn read-regex
  [rdr ch]
  (let [sb (StringBuilder.)]
    (loop [ch (read-char rdr)]
      (if (identical? \" ch)
        (Pattern/compile (str sb))
        (if (nil? ch)
          (reader-error rdr "EOF while reading regex")
          (do
            (.append sb ch )
            (when (identical? \\ ch)
              (let [ch (read-char rdr)]
                (if (nil? ch)
                  (reader-error rdr "EOF while reading regex"))
                (.append sb ch)))
            (recur (read-char rdr))))))))

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
      ((wrapping-reader 'carthy.core/unquote-splicing) (doto rdr read-char) \@)
      ((wrapping-reader 'carthy.core/unquote) rdr \~))))

(declare syntax-quote)
(defn unquote-splicing? [form]
  (and (seq? form)
       (= (first form) 'carthy.core/unquote-splicing)))

(defn unquote? [form]
  (and (seq? form)
       (= (first form) 'carthy.core/unquote)))

(defn- register-gensym [sym]
  (if-not gensym-env
    (throw (IllegalStateException. "Gensym literal not in syntax-quote")))
  (or (get gensym-env sym)
      (let [gs (symbol (str (subs (name sym)
                                  0 (dec (count (name sym))))
                            "__" (RT/nextID) "__auto__"))]
        (set! gensym-env (assoc gensym-env sym gs))
        gs)))

;; TODO: should move those two to use the runtime
(defn- resolve-ns [sym]
  (or ((ns-aliases *ns*) sym)
      (find-ns sym)))

(defn- resolve-symbol [s]
  (if-let [ns-str (namespace s)]
    (let [^Namespace ns (resolve-ns (symbol ns-str))
          ns-name (name (.name ns))]
      (if (or (nil? ns)
              (= ns-name ns-str)) ;; not an alias
        s
        (symbol ns-name (name s))))
    (if-let [o ((ns-map *ns*) s)] ;; refered symbol
      (symbol (-> ^Var o .ns .name name)
              (-> ^Var o .sym name))
      (symbol (name (.name *ns*)) (name s)))))

(defn- add-meta [form ret]
  (if (and (instance? IObj form)
           (dissoc (meta form) :line :column))
    (list 'carthy.core/with-meta ret (syntax-quote (meta form)))
    ret))

(defn syntax-quote [form]
  (->>
   (cond

     (special-symbol? form)
     form

     (symbol? form)
     (or
      (when-not (namespace form)
        (let [sym (name form)]
          (cond
            (.endsWith sym "#")
            (register-gensym form)

            (.startsWith sym ".")
            form

            (.startsWith sym "$") ;; == '~
            (symbol (subs sym 1)))))
      (resolve-symbol form))

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
    (list 'carthy.core/syntax-quote
          (syntax-quote (read rdr true nil true)))))

(defn read-heredoc [rdr e]
  (let [eof (loop [s ""]
              (let [c (read-char rdr)]
                (if (= e c)
                  s
                  (recur (str s c)))))
        text (loop [s "" pb ""]
               (let [r (read-char rdr)]
                 (if (= eof (str pb r))
                   s
                   (if r
                     (if (= r (nth eof
                                   (count pb)))
                      (recur s (str pb r))
                      (recur (str s pb r) ""))
                     (reader-error rdr "EOF while reading string")))))]
    text))

(defn macros [ch]
  (case ch
    \" read-string*
    \: read-keyword
    \; read-comment
    \' (wrapping-reader 'quote)
    \@ (wrapping-reader 'carthy.core/deref)
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
    \> read-heredoc
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
      (let [entries (to-array (read-delimited end-ch rdr true))
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

(defn queue-reader [form]
  {:pre [(vector? form)]}
  (into PersistentQueue/EMPTY form))

(defmethod print-method PersistentQueue [^PersistentQueue q ^java.io.Writer w]
  (.write w (str "#queue " (vec q))))

(def default-data-readers
  (assoc c.c/default-data-readers
    'c #'complex-reader
    'bitmap #'bitmap-reader
    'queue #'queue-reader))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Public API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn read
  "Reads the first object from an IPushbackReader or a java.io.PushbackReader.
Returns the object read. If EOF, throws if eof-error? is true. Otherwise returns sentinel."
  ([] (read *in*))
  ([reader] (read reader true nil))
  ([reader eof-error? sentinel] (read reader eof-error? sentinel false))
  ([reader eof-error? sentinel recursive?]
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
                                   (when (indexing-reader? reader)
                                     {:line (get-line-number reader)
                                      :column (get-column-number reader)}))
                            e)))))))

(defn read-string
  "Reads one object from the string s"
  [s]
  (read (string-push-back-reader s) true nil false))
