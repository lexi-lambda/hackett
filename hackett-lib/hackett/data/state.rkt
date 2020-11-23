#lang hackett

; a simple State, with Monad/Applicative/Functor instances
; with operations 'put', 'get' and 'modify' to run in the Monad.
; See also 'runState' and 'runUndefinedState'

#| Example

; define a State with Integer as the internal state.

(def stateInteger : (State Integer (List Integer))
     (do
       (put 42)                     ; set the internal state
       [i1 <- get]                  ; query the internal state
       (modify (+ 10))              ; modify the internal state, adding 10 to it
       [i2 <- get]                  ; query again
       (modify (+ 10))              ; modify again
       (pure {i1 :: i2 :: nil})))   ; return the two intermediate internal states
     ))

(main {(runUndefinedState stateInteger ) & show & println})
 |#


(provide (data State) put get modify runState runUndefinedState)

(data (State s a) (state {s -> { s Tuple a }}))

(instance (forall [a] (Functor (State a)))
  [map (λ [f (state mx)] (state (λ [rw] (case (mx rw) [(tuple rw* a) (tuple rw* (f a))]))))])

(instance (forall [a] (Applicative (State a)))
  [pure (λ [x] (state (λ [rw] (tuple rw x))))]
  [<*>  undefined!])

(instance (forall [a] (Monad (State a)))
  [join (λ [(state outer)] (state (λ [rw]
                                     (case (outer rw)
                                       [(tuple rw* m-inner) (case m-inner [(state inner) (inner rw*)])]))))])

(defn put : (forall [a] {a -> (State a Unit)})
  [[s] (state (λ [_] {s tuple unit}))])
(def get : (forall [a] (State a a))
  (state (λ [s] {s tuple s})))
(defn modify : (forall [a] {{a -> a} -> (State a Unit)})
  [[modifier] (state (λ [rw] {(modifier rw) tuple unit}))])

(defn runState
      [[(state mx) initialstate]
       (case (mx initialstate) [(tuple a b) (tuple b a)])
       ])

(def runUndefinedState ((flip runState) undefined!)) ; if the first step is 'put', then the initial state doesn't matter and we can use undefined! as the initial state
