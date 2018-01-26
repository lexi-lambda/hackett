#lang hackett

(require hackett/monad/error
         hackett/monad/reader
         hackett/monad/trans

         (rename-in hackett
                    [print print/mono]
                    [println println/mono]))

(class (Monad m) => (MonadIO m)
  [lift/io : (forall [a] {(IO a) -> (m a)})])

(instance (MonadIO IO)
  [lift/io id])

(instance (forall [r m] (MonadIO m) => (MonadIO (ReaderT r m)))
  [lift/io {lift . lift/io}])

(instance (forall [e m] (MonadIO m) => (MonadIO (ErrorT e m)))
  [lift/io {lift . lift/io}])


(def print : (forall [m] (MonadIO m) => {String -> (m Unit)})
  {lift/io . print/mono})

(def println : (forall [m] (MonadIO m) => {String -> (m Unit)})
  {lift/io . println/mono})


(main (run-reader-t (do [name <- ask]
                        (println {"Hello, " ++ name ++ "!"}))
                    "Alexis"))
