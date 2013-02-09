(ns glasses.utils
  (:refer-clojure :exclude [char]))

(defn char [x]
  (when x
    (clojure.core/char x)))

(defn whitespace?
  "Checks whether a given character is whitespace"
  [ch]
  (when ch
    (or (Character/isWhitespace ^Character ch)
        (identical? \, ch))))

(defn numeric?
  "Checks whether a given character is numeric"
  [^Character ch]
  (when ch
    (Character/isDigit ch)))

(defn comment-prefix?
  "Checks whether the character begins a comment."
  [ch]
  (identical? \; ch))

(defn newline? [c]
  "Checks whether the character is a newline"
  (or (identical? \newline c)
      (nil? c)))
