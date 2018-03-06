#lang hackett

(require hackett/monad/trans)

(provide (for-type StateT)
         runStateT
         state
         evalStateT
         execStateT
         mapStateT
         withStateT
         get
         put
         modify
         gets)
         

;; adapted from
;; https://github.com/ghc/packages-transformers/blob/master/Control/Monad/Trans/State/Lazy.hs

;; Lazy state monads, passing an updatable state through a computation.
;; See below for examples.
;;
;; Some computations may not require the full power of state transformers:
;;
;; * For a read-only state, see "Control.Monad.Trans.Reader".
;;
;; * To accumulate a value without using it on the way, see
;;   "Control.Monad.Trans.Writer".
;;
;; In this version, sequencing of computations is lazy, so that for
;; example the following produces a usable result:
;;
;; > evalState (sequence $ repeat $ do { n <- get; put (n*2); return n }) 1
;;
;; For a strict version with the same interface, see
;; "Control.Monad.Trans.State.Strict".

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A state monad parameterized by the type @s@ of the state to carry.
;;
;; The 'return' function leaves the state unchanged, while @>>=@ uses
;; the final state of the first computation as the initial state of
;; the second.
;; type State s = StateT s Identity

#|


-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState :: State s a   -- ^state-passing computation to execute
         -> s           -- ^initial state
         -> (a, s)      -- ^return value and final state
runState m = runIdentity . runStateT m
{-# INLINE runState #-}

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalState' m s = 'fst' ('runState' m s)@
evalState :: State s a  -- ^state-passing computation to execute
          -> s          -- ^initial value
          -> a          -- ^return value of the state computation
evalState m s = fst (runState m s)
{-# INLINE evalState #-}

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execState' m s = 'snd' ('runState' m s)@
execState :: State s a  -- ^state-passing computation to execute
          -> s          -- ^initial value
          -> s          -- ^final state
execState m s = snd (runState m s)
{-# INLINE execState #-}

-- | Map both the return value and final state of a computation using
-- the given function.
--
-- * @'runState' ('mapState' f m) = f . 'runState' m@
mapState :: ((a, s) -> (b, s)) -> State s a -> State s b
mapState f = mapStateT (Identity . f . runIdentity)
{-# INLINE mapState #-}

-- | @'withState' f m@ executes action @m@ on a state modified by
-- applying @f@.
--
-- * @'withState' f m = 'modify' f >> m@
withState :: (s -> s) -> State s a -> State s a
withState = withStateT
{-# INLINE withState #-}
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; this doesn't belong here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(instance (∀ [a b] (Semigroup a) (Semigroup b) => (Semigroup (Tuple a b)))
  [++ (λ* [[(Tuple a1 b1) (Tuple a2 b2)]
           (Tuple {a1 ++ a2} {b1 ++ b2})])])

(instance (∀ [a b] (Monoid a) (Monoid b) => (Monoid (Tuple a b)))
  [mempty (Tuple mempty mempty)])

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A state transformer monad parameterized by:
;;
;;   * @s@ - The state.
;;
;;   * @m@ - The inner monad.
;;
;; The 'return' function leaves the state unchanged, while @>>=@ uses
;; the final state of the first computation as the initial state of
;; the second.

(data (StateT s m a)
      (StateT {s -> (m (Tuple a s))}))

(defn runStateT
  [[(StateT f)] f])

;; Construct a state monad computation from a function.
;; (The inverse of 'runState'.)
(defn state : (∀ [m s a] (Monad m) =>
                 {{s -> (Tuple a s)} -> (StateT s m a)})
  [[f] (StateT {pure . f})])

;; Evaluate a state computation with the given initial state
;; and return the final value, discarding the final state.
;;
;; * @'evalStateT' m s = 'liftM' 'fst' ('runStateT' m s)@
(defn evalStateT : (∀ [m s a] (Monad m) => {(StateT s m a) -> s -> (m a)})
  [[m s]
   (do [t <- (runStateT m s)] ;; this originally used a lazy pattern
     (case t
       [(Tuple a _)
        (pure a)]))])

;; Evaluate a state computation with the given initial state
;; and return the final state, discarding the final value.
;;
;; * @'execStateT' m s = 'liftM' 'snd' ('runStateT' m s)@
(defn execStateT : (∀ [m s a] (Monad m) => {(StateT s m a) -> s -> (m s)})
  [[m s]
   (do [t <- (runStateT m s)] ;; this originally used a lazy pattern
     (case t
       [(Tuple _ s2)
        (pure s2)]))])

;; Map both the return value and final state of a computation using
;; the given function.
;;
;; * @'runStateT' ('mapStateT' f m) = f . 'runStateT' m@
(defn mapStateT : (∀ [m n s a b] {{(m (Tuple a s)) -> (n (Tuple b s))}
                                  -> (StateT s m a)
                                  -> (StateT s n b)})
  [[f m] (StateT {f . (runStateT m)})])

;; @'withStateT' f m@ executes action @m@ on a state modified by
;; applying @f@.
;;
;; * @'withStateT' f m = 'modify' f >> m@
(defn withStateT : (∀ [s m a] {{s -> s} -> (StateT s m a) -> (StateT s m a)})
  [[f m] (StateT {(runStateT m) . f})])

(instance (∀ [m s] (Functor m) => (Functor (StateT s m)))
  [map
   (λ [f m]
     (StateT (λ [s]
               (map (λ [t] (case t
                             [(Tuple a sp) (Tuple (f a) sp)]))
                    (runStateT m s)))))])

(instance (∀ [m s] (Monad m) => (Applicative (StateT s m)))
  [pure (λ [a] (StateT (λ [s] (pure (Tuple a s)))))]
  [<*>
   (λ* [[(StateT mf) (StateT mx)]
        (StateT (λ [s] (do [t1 <- (mf s)]
                         [t2 <- (case t1
                                  [(Tuple f sp) (mx sp)])]
                         ;; because binding positions aren't patterns we have to match on t1 again to
                         ;; get f (or use a nested `do`)
                         (case* [t1 t2]
                           [[(Tuple f _) (Tuple x spp)] (pure (Tuple (f x) spp))]))))])])

;; not sure where this goes wrong

;; this was originally an Alternative instance in terms of MonadPlus but I'm going to venture to say
;; Monoid subsumes both those classes in Hackett
#;(instance (∀ [m s a] (Monad m) (Monoid m) => (Semigroup (StateT s m a)))
  [++
   (λ* [[(StateT m) (StateT n)]
        (StateT (λ [s] {(m s) ++ (n s)}))])])


#;(instance (∀ [m s] (Monad m) (Monoid m) => (Monoid (StateT s m)))
  [mempty (StateT (λ [_] mempty))])

(instance (∀ [m s] (Monad m) => (Monad (StateT s m)))
  [=<<
   (λ* [[k m]
        (StateT (λ [s] (do [t <- (runStateT m s)]
                         (case t
                           [(Tuple a sp)
                            (runStateT (k a) sp)]))))])])

(instance (∀ [s] (MonadTrans (StateT s)))
  [lift
   (λ [m] (StateT (λ [s] (do [a <- m]
                           (pure (Tuple a s))))))])

;; Fetch the current value of the state within the monad.
(def get : (∀ [m s] (Monad m) => (StateT s m s))
  (state (λ [s] (Tuple s s))))

;; @'put' s@ sets the state within the monad to @s@.
(defn put : (∀ [m s] (Monad m) => {s -> (StateT s m Unit)})
  [[s] (state (λ [_] (Tuple Unit s)))])

;; @'modify' f@ is an action that updates the state to the result of
;; applying @f@ to the current state.
;;
;; * @'modify' f = 'get' >>= ('put' . f)@
(defn modify : (∀ [m s] (Monad m) => {{s -> s} -> (StateT s m Unit)})
  [[f] (state (λ [s] (Tuple Unit (f s))))])

;; Get a specific component of the state, using a projection function
;; supplied.
;;
;; * @'gets' f = 'liftM' f 'get'@
(defn gets : (∀ [m s a] (Monad m) => {{s -> a} -> (StateT s m a)})
  [[f] (state (λ [s] (Tuple (f s) s)))])

#|

instance (Functor m, MonadPlus m) => Alternative (StateT s m) where
    empty = StateT $ \ _ -> mzero
    {-# INLINE empty #-}
    StateT m <|> StateT n = StateT $ \ s -> m s `mplus` n s
    {-# INLINE (<|>) #-}


#if MIN_VERSION_base(4,9,0)
instance (Fail.MonadFail m) => Fail.MonadFail (StateT s m) where
    fail str = StateT $ \ _ -> Fail.fail str
    {-# INLINE fail #-}
#endif

instance (MonadPlus m) => MonadPlus (StateT s m) where
    mzero       = StateT $ \ _ -> mzero
    {-# INLINE mzero #-}
    StateT m `mplus` StateT n = StateT $ \ s -> m s `mplus` n s
    {-# INLINE mplus #-}

instance (MonadFix m) => MonadFix (StateT s m) where
    mfix f = StateT $ \ s -> mfix $ \ ~(a, _) -> runStateT (f a) s
    {-# INLINE mfix #-}

instance MonadTrans (StateT s) where
    lift m = StateT $ \ s -> do
        a <- m
        return (a, s)
    {-# INLINE lift #-}

instance (MonadIO m) => MonadIO (StateT s m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}



-- | A variant of 'modify' in which the computation is strict in the
-- new state.
--
-- * @'modify'' f = 'get' >>= (('$!') 'put' . f)@
modify' :: (Monad m) => (s -> s) -> StateT s m ()
modify' f = do
    s <- get
    put $! f s
{-# INLINE modify' #-}



-- | Uniform lifting of a @callCC@ operation to the new monad.
-- This version rolls back to the original state on entering the
-- continuation.
liftCallCC :: CallCC m (a,s) (b,s) -> CallCC (StateT s m) a b
liftCallCC callCC f = StateT $ \ s ->
    callCC $ \ c ->
    runStateT (f (\ a -> StateT $ \ _ -> c (a, s))) s
{-# INLINE liftCallCC #-}

-- | In-situ lifting of a @callCC@ operation to the new monad.
-- This version uses the current state on entering the continuation.
-- It does not satisfy the uniformity property (see "Control.Monad.Signatures").
liftCallCC' :: CallCC m (a,s) (b,s) -> CallCC (StateT s m) a b
liftCallCC' callCC f = StateT $ \ s ->
    callCC $ \ c ->
    runStateT (f (\ a -> StateT $ \ s' -> c (a, s'))) s
{-# INLINE liftCallCC' #-}

-- | Lift a @catchE@ operation to the new monad.
liftCatch :: Catch e m (a,s) -> Catch e (StateT s m) a
liftCatch catchE m h =
    StateT $ \ s -> runStateT m s `catchE` \ e -> runStateT (h e) s
{-# INLINE liftCatch #-}

-- | Lift a @listen@ operation to the new monad.
liftListen :: (Monad m) => Listen w m (a,s) -> Listen w (StateT s m) a
liftListen listen m = StateT $ \ s -> do
    ~((a, s'), w) <- listen (runStateT m s)
    return ((a, w), s')
{-# INLINE liftListen #-}

-- | Lift a @pass@ operation to the new monad.
liftPass :: (Monad m) => Pass w m (a,s) -> Pass w (StateT s m) a
liftPass pass m = StateT $ \ s -> pass $ do
    ~((a, f), s') <- runStateT m s
    return ((a, s'), f)
{-# INLINE liftPass #-}
|#