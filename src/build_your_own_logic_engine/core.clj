(ns build-your-own-logic-engine.core
  (:refer-clojure :exclude [==])
  (:require [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.pprint :refer [pprint]]
            [clojure.set :as set])
  (:import (java.io Writer)
           (clojure.lang IDeref)))

;; Paper that describes the basic concepts we'll be using today
;; http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf

;; We are building a interpreter of sorts, so the first thing we need to do is
;; define what we're going to use for "locals" and how they are stored. We will call
;; these locals "logic variables" or "lvars" for short.

(defn lvar
  ([]
   (gensym))
  ([prefix]
   (gensym prefix)))

(defn lvar?
  "Is this a lvar?"
  [v]
  (symbol? v))

(defn walk [env v]
  (if-let [[_ nv] (find env v)]
    (recur env nv)
    v))

(defn grounded?
  "Is this value not a lvar?, and optionally takes an environment."
  ([v]
   (not (lvar? v)))
  ([env v]
   (not (lvar? (walk env v)))))

(comment

  (lvar)
  (lvar "foo")

  (let [a (lvar "a")]
    (walk {a 1} a))

  (let [a (lvar "a")
        b (lvar "b")]
    (walk {a 1} b))

  (let [a (lvar "a")
        b (lvar "b")]
    (walk {a 1 b a} b))


  (let [a (lvar "a")]
    (lvar? (walk {a 1} a)))

  (let [a (lvar "a")]
    (grounded? (walk {a 1} a)))

  (let [a (lvar "a")]
    (grounded? {a 1} a))

  )

;; The next main primitive we need is "unify" or the process of checking if two lvars
;; can be equal given an environment.

(defn unify [env a b]
  (let [a' (walk env a)
        b' (walk env b)]
    (cond
      (nil? env) env

      (and (lvar? a')
           (lvar? b')) (assoc env a' b')

      (lvar? a') (assoc env a' b')
      (lvar? b') (assoc env b' a')

      :else
      (when (= a' b') env))))

(comment
  (unify {} 1 2)
  (unify {} 1 1)

  (unify {'a 4} 'a 'b)

  (unify {} 'a 'b)

  (-> {}
      (unify 'a 'b)
      (unify 'b 4)
      (walk 'a))

  )

;; Now that we have the primitives of our language we can start to build a DSL
;; We will dealing with streams of environments. We can use almost any construct
;; that deals with streams of values, but today we'll use transducers.

(defn == [a b]
  (keep #(unify % a b)))

(comment
  (transduce
    (== 'a 42)
    conj
    [{}])

  )

;; That doesn't give us much, so now we need to define a logical "and" or a conjunction

(defn conjunction [& clauses]
  (apply comp clauses))

;; or....

(def conjunction comp)

(comment

  (transduce
    (conjunction
      (== 'a 42)
      (== 'b 33))
    conj
    [{}])

  (transduce
    (conjunction
      (== 'a 42)
      (== 'b 33)
      (== 'a 'b))
    conj
    [{}])

  (transduce
    (conjunction
      (== 'a 42)
      (== 'b 'a))
    conj
    [{}])

  )


;; It's rather hard to figure out what's going on in the results here, so let's write
;; a "extract" lvars from results.

(defn -extractor [sym]
  (fn [env]
    (walk env sym)))

(defn extract [& lvars]
  (map (apply juxt
              (map -extractor lvars))))


(comment

  (transduce
    (conjunction
      (== 'a 42)
      (== 'b 33)
      (extract 'a 'b))
    conj
    [{}])

  )

;; And now for logical "or" or a disjunction. In this case we want to pass all
;; the environments into each of the sub-clauses.

;; Copied from clojure.core
(defn ^:private preserving-reduced
  [rf]
  #(let [ret (rf %1 %2)]
     (if (reduced? ret)
       (reduced ret)
       ret)))

(defn disjunction [& exprs]
  (fn [xf]
    (let [fs (mapv (fn [expr]
                     (preserving-reduced (expr xf)))
                   exprs)]
      (fn
        ([] (xf))
        ([acc] (xf acc))
        ([acc itm]
         (reduce #(%2 %1 itm) acc fs))))))

(comment

  (transduce
    (disjunction
      (== 'a 42)
      (== 'b 33))
    conj
    [{}])

  (transduce
    (disjunction
      (== 'a 42)
      (== 'a 33))
    conj
    [{}])

  (transduce
    (conjunction
      (disjunction
        (== 'a 42)
        (== 'a 33))
      (== 'b 'a))
    conj
    [{}])

  (transduce
    (conjunction
      (disjunction
        (== 'a 42)
        (== 'a 33))
      (== 'a 33))
    conj
    [{}])

  (transduce
    (conjunction
      (== 'a 33)
      (disjunction
        (== 'a 42)
        (== 'a 33)))
    conj
    [{}])

  (transduce
    (conjunction
      (== 'b 33)
      (== 'a 'b)
      (disjunction
        (== 'a 42)
        (== 'a 33)))
    conj
    [{}])

  (transduce
    (conjunction
      (== 'b 33)
      (disjunction
        (== 'a 42)
        (== 'a 33))
      (== 'a 'b))
    conj
    [{}])

  ;; These all look the same, but they do have different performance profiles.

  )

;; Let's encapsulate the common logic here

(defn run [& clauses]
  (transduce (apply conjunction clauses) conj [{}]))

(comment
  (run (== 1 'a))

  )


;; Let's make a database

(deftype EntID [])

(defmethod print-method EntID
  [x ^Writer w]
  (.write w (str "id@" (System/identityHashCode x))))

(defn parse-value [v]
  (let [result (try
                 (edn/read-string v)
                 (catch Throwable _ v))]
    (if (symbol? result)
      (name result)
      result)))

(defn load-csv [filename]
  (with-open [reader (io/reader (io/resource filename))]
    (let [[head & tail] (csv/read-csv reader)
          head (map keyword head)]
      (mapv
        (fn [ks vs]
          (zipmap ks (map parse-value vs)))
        (repeat head)
        tail))))



(defn tuples-for-data [data]
  (mapcat
    (fn [mp]
      (let [id (->EntID)]
        (for [[k v] mp]
          [id k v])))
    data))

(defn categorize-system [{:keys [security] :as system}]
  (let [sec-status (cond
                     (>= security 0.5) :high
                     (> security 0) :low
                     :else :null)]
    (assoc system :sec-status sec-status)))

(def solar-systems (->> "mapSolarSystems.csv"
                        load-csv
                        (map categorize-system)
                        tuples-for-data))

(def system-jumps (-> "mapSolarSystemJumps.csv"
                      load-csv
                      tuples-for-data))

(comment
  (pprint
    (take 100 solar-systems))
  (take 10 system-jumps)

  (into #{} (map :security) (load-csv "mapSolarSystems.csv"))

  (count solar-systems)

  )

(def s-conj (fnil conj #{}))

(defn index-data [data a b]
  (reduce
    (fn [index tuple]
      (update-in index [(tuple a) (tuple b)] s-conj tuple))
    {}
    data))

(alter-var-root #'index-data memoize)

(comment

  (time (count (index-data solar-systems 0 1)))

  [ent :solarSystemName "Jita"]

  )

(defn index-for
  ([data a b av]
   (let [idx (index-data data a b)]
     (vec (apply concat (vals (get-in idx [av]))))))
  ([data a b av bv]
   (let [idx (index-data data a b)]
     (get-in idx [av bv]))))


(defn q [data e a v]
  (mapcat
    (fn [env]
      (->> (let [e' (walk env e)
                 a' (walk env a)
                 v' (walk env v)]
             (condp = [(grounded? e') (grounded? a') (grounded? v')]
               [false true true] (for [[e] (index-for data 1 2 a' v')]
                                   (unify env e e'))
               [true true false] (for [[_ _ v] (index-for data 0 1 e' a')]
                                   (unify env v v'))
               [false true false] (for [[e _ v] (index-for data 1 2 a')]
                                    (-> env
                                        (unify e e')
                                        (unify v v')))
               [true true true] (for [[_ _ v] (index-for data 0 1 e' a')]
                                  (unify env v v'))))
           (remove nil?)))))

(defmacro with-fresh [& body]
  (let [lvars (->> body
                   flatten
                   (filter simple-symbol?)
                   (remove #(contains? &env %))
                   (filter #(str/starts-with? (name %) "?")))]
    `(let [~@(interleave
               lvars
               (map
                 (fn [sym]
                   `(gensym ~(name sym)))
                 lvars))]
       ~@body)))

(comment

  (macroexpand '(with-fresh ?e ?a))

  (with-fresh
    (run
      (q solar-systems ?id :solarSystemName "Jita")
      (q solar-systems ?id :sec-status ?sec)
      (extract ?sec)))

  (with-fresh
    (run
      (q solar-systems ?id :sec-status :high)
      (q solar-systems ?id :solarSystemName ?name)
      (extract ?name)))

  (with-fresh
    (run
      (q solar-systems ?id :solarSystemName ?name)
      (q solar-systems ?id :sec-status :high)
      (extract ?name)))

  )

;; We can write query composers to move up a level of abstraction
(defn jumps-to [?from ?to]
  (with-fresh
    (conjunction
      (q solar-systems ?from :solarSystemID ?from-id)
      (q system-jumps ?jump :fromSolarSystemID ?from-id)
      (q system-jumps ?jump :toSolarSystemID ?to-id)
      (q solar-systems ?to :solarSystemID ?to-id))))

(comment
  ;; Keys in system jumps table
  (into #{} (map second system-jumps))
  (into #{} (map second solar-systems))

  ;; Systems connected to Jita
  (with-fresh
    (run
      (q solar-systems ?jita :solarSystemName "Jita")
      (jumps-to ?jita ?to)
      (q solar-systems ?to :solarSystemName ?to-name)
      (extract ?to-name)))

  ;; Border Systems (low sec that jumps to high sec)
  (with-fresh
    (run
      (q solar-systems ?from :sec-status :low)
      (q solar-systems ?from :solarSystemName ?from-name)
      (jumps-to ?from ?to)
      (q solar-systems ?to :sec-status :high)
      (q solar-systems ?to :solarSystemName ?to-name)

      ;; Grab real sec of both systems
      (q solar-systems ?from :security ?from-sec)
      (q solar-systems ?to :security ?to-sec)
      (extract ?from-name ?from-sec ?to-name ?to-sec)))

  ;; Systems that have both high and low neighbors (30ms on my system)
  (time
    (with-fresh
      (run
        (q solar-systems ?low :sec-status :low)
        (q solar-systems ?low :solarSystemName ?low-name)
        (jumps-to ?low ?high)
        (q solar-systems ?high :sec-status :high)
        (q solar-systems ?high :solarSystemName ?high-name)
        (jumps-to ?low ?null)
        (q solar-systems ?null :sec-status :null)
        (q solar-systems ?null :solarSystemName ?null-name)

        (extract ?null-name ?low-name ?high-name))))


  (count
    (with-fresh
      (run
        (q solar-systems ?id :solarSystemName ?name))))

  ;; DON'T RUN!
  ;; Same as prev, but with bad ordering, never completes
  (time
    (with-fresh
      (run
        (q solar-systems ?low :sec-status :low)             ; 8K stars
        (q solar-systems ?high :sec-status :high)           ; * 8K stars
        (q solar-systems ?null :sec-status :null)           ; * 8K stars

        (jumps-to ?low ?high)                               ; 512 billion combinations
        (jumps-to ?low ?null)

        (q solar-systems ?low :solarSystemName ?low-name)
        (q solar-systems ?high :solarSystemName ?high-name)
        (q solar-systems ?null :solarSystemName ?null-name)

        (extract ?null-name ?low-name ?high-name))))

  )

;; Let's think about representing the queries as ASTs

(defn q-ast [data e a v]
  (assert (var? data))
  {:op :q
   :e e
   :a a
   :v v
   :data data})

(defn and-ast [& clauses]
  (let [clauses (mapcat
                  (fn [{:keys [op clauses] :as clause}]
                    (if (= op :and)
                      clauses
                      [clause]))
                  clauses)]
    {:op :and
     :clauses (vec clauses)}))

(defn extract-ast [& lvars]
  {:op :extract
   :lvars (vec lvars)})

(defn jumps-to-ast [?from ?to]
  (with-fresh
    (and-ast
      (q-ast #'solar-systems ?from :solarSystemID ?from-id)
      (q-ast #'system-jumps ?jump :fromSolarSystemID ?from-id)
      (q-ast #'system-jumps ?jump :toSolarSystemID ?to-id)
      (q-ast #'solar-systems ?to :solarSystemID ?to-id))))

(comment

  ;; Print the constructed AST
  (pprint
    (with-fresh
      (and-ast
        (q-ast #'solar-systems ?low :sec-status :low)         ; 8K stars
        (q-ast #'solar-systems ?high :sec-status :high)       ; * 8K stars
        (q-ast #'solar-systems ?null :sec-status :null)       ; * 8K stars

        (jumps-to-ast ?low ?high)                           ; 512 billion combinations
        (jumps-to-ast ?low ?null)

        (q-ast #'solar-systems ?low :solarSystemName ?low-name)
        (q-ast #'solar-systems ?high :solarSystemName ?high-name)
        (q-ast #'solar-systems ?null :solarSystemName ?null-name)

        (extract-ast ?null-name ?low-name ?high-name))))

  )


;; Now let's write an AST sorter
(defmulti attempt-sort (fn [bound {:keys [op]}]
                         op))

(defmethod attempt-sort :and
  [bound {:keys [clauses]}]
  (let [extracts (filter #(= (:op %) :extract) clauses)
        clauses (remove (set extracts) clauses)]

    ;; so now we'll loop, finding clauses that can bind against
    (loop [bound bound
           remain (set clauses)
           sorted []]
      (if (seq remain)
        (let [next-node (->> remain
                             (keep #(attempt-sort bound %))
                             ;; Only perform left-joins
                             (filter #(set/subset? bound (:join/bound %)))
                             (sort-by :join/cost)
                             first)]
          (assert next-node "Can't sort, can't find next node!")
          (recur (set/union bound (:join/bound next-node))
                 (disj remain (dissoc next-node :join/bound :join/cost))
                 (conj sorted (assoc next-node :join/pre-bound bound))))
        {:op :and
         :clauses (vec (concat sorted extracts))}))))

(defn average-size [colls]
  (let [sizes (mapv count colls)]
    (/ (reduce + 0 sizes)
       (count sizes))))

(let [grounded? (fn [bound v]
                  (cond
                    (grounded? v) :const
                    (contains? bound v) :bound
                    :else :unbound))
      index-for (memoize
                  (fn [data & args]
                    (apply index-for @data args)))
      ;; This counting needs to be cached to get fast query sorting. There's dozens ways
      ;; of doing this, this is a quick-and-dirty method. Production code should use something
      ;; much more robust.
      calc-bcu (memoize
                 (fn [data a]
                   (average-size (group-by first (index-for data 1 0 a)))))
      calc-ucb (memoize
                 (fn [data a]
                   (average-size (group-by last (index-for data 1 2 a)))))]

  (defmethod attempt-sort :q
    [bound {:keys [e a v data] :as node}]
    (condp = [(grounded? bound e) (grounded? bound a) (grounded? bound v)]
      [:unbound :const :unbound] (assoc node :join/bound (conj bound e v)
                                             :join/cost (count (index-for data 1 2 a)))
      [:bound :const :bound] (assoc node :join/bound bound
                                         :join/cost 1)
      [:unbound :const :const] (assoc node :join/bound (conj bound e v)
                                           :join/cost (count (index-for data 1 2 a v)))

      [:bound :const :unbound] (assoc node :join/bound (conj bound v)
                                           :join/cost (calc-bcu data a))
      [:bound :const :const] (assoc node :join/bound (conj bound e v)
                                         :join/cost 1)
      [:unbound :const :bound] (assoc node :join/bound (conj bound e)
                                           :join/cost (calc-ucb data a)))))

(comment

  (def q-ast (with-fresh
               (and-ast
                 (q-ast #'solar-systems ?low :sec-status :low) ; 8K stars
                 (q-ast #'solar-systems ?high :sec-status :high) ; * 8K stars
                 (q-ast #'solar-systems ?null :sec-status :null) ; * 8K stars

                 (jumps-to-ast ?low ?high)                  ; 512 billion combinations
                 (jumps-to-ast ?low ?null)

                 (q-ast #'solar-systems ?low :solarSystemName ?low-name)
                 (q-ast #'solar-systems ?high :solarSystemName ?high-name)
                 (q-ast #'solar-systems ?null :solarSystemName ?null-name)

                 (extract-ast ?null-name ?low-name ?high-name))))

  (def q-ast-sorted (time (attempt-sort #{} q-ast)))

  (pprint (map (juxt :e :a :v) (:clauses q-ast-sorted)))

  )

(defmulti gen-query :op)

(defmethod gen-query :and
  [{:keys [clauses]}]
  (apply conjunction (map gen-query clauses)))

(defmethod gen-query :q
  [{:keys [data e a v]}]
  (q @data e a v))

(defmethod gen-query :extract
  [{:keys [lvars]}]
  (apply extract lvars))

(comment

  (time (run (gen-query q-ast-sorted)))

  )

(def gen-clj nil)
(defmulti gen-clj (fn [inner {:keys [op]}]
                     op))

(defmethod gen-clj :and
  [inner {:keys [clauses]}]
  (reduce
    gen-clj
    inner
    (reverse clauses)))

(defmethod gen-clj :extract
  [inner {:keys [lvars]}]
  `(let [~'result ~(vec lvars)]
     ~inner))

(defmacro sdoseq
  "Simple doseq"
  [[bind coll] & body]
  `(loop [result# (seq ~coll)]
     (when (seq result#)
       (let [~bind (first result#)]
         ~@body
         (recur (next result#))))))

(let [grounded? (fn [bound v]
                  (cond
                    (grounded? v) :const
                    (contains? bound v) :bound
                    :else :unbound))]
  (defmethod gen-clj :q
    [inner {:keys [e a v join/pre-bound ^clojure.lang.Var data]}]
    (let [data (symbol
                 (name (.-name (.-ns data)))
                 (name (.-sym data)))]
      (condp = [(grounded? pre-bound e) (grounded? pre-bound a) (grounded? pre-bound v)]

        [:bound :const :unbound]
        `(sdoseq [[~'_ ~'_ ~v] (~'index-for (~'deref (var ~data)) 0 1 ~e ~a)]
           ~inner)

        [:bound :const :const]
        `(sdoseq [[~'_ ~'_ v#] (~'index-for (~'deref (var ~data)) 0 1 ~e ~a)]
           (when (= v# ~v)
             ~inner))

        [:unbound :const :bound]
        `(sdoseq [[~e] (~'index-for (~'deref (var ~data)) 1 2 ~a ~v)]
           ~inner)

        [:unbound :const :unbound]
        `(sdoseq [[~e ~'_ ~v] (~'index-for (~'deref (var ~data)) 1 0 ~a)]
           ~inner)

        [:unbound :const :const]
        `(sdoseq [[~e] (~'index-for (~'deref (var ~data)) 1 2 ~a ~v)]
           ~inner)))))

(defn compile [ast]
  (let [sexpr `(fn []
                 (let [~'results (volatile! (transient []))]
                   ~(gen-clj `(vswap! ~'results conj! ~'result) ast)
                   (persistent! @~'results)))]
    (eval sexpr)))

(comment

  (sdoseq [[x y] (map (juxt inc dec) (range 10))]
          (println [x y]))

  (pprint (gen-clj `(identity ~'result) q-ast-sorted))

  (index-for (deref #'solar-systems 1 0 :sec))

  (time (compile q-ast-sorted))

  (time ((compile q-ast-sorted)))

  (let [f (compile q-ast-sorted)]
    (dotimes [x 100]
      (time (f))))

  )

;; Points of future extension
;; 1) Use nested cases instead of condp
;; 2) Allow parameters to be passed to compiled functions
;; 3) Support merge joins
;; 4) Support recursive rules
;; 5) Support partial evaluation (with code-expressions?)


