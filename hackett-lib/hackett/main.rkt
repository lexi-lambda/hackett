#lang racket/base

(require syntax/parse/define

         hackett/prelude
         (only-in hackett/private/adt case* case λ λ* lambda lambda* defn _)
         (only-in hackett/private/class instance)
         (except-in hackett/private/kernel λ lambda #%module-begin)
         (only-in hackett/private/kernel [#%module-begin @%module-begin/nonconfigured])
         hackett/private/provide
         (only-in hackett/private/toplevel @%top-interaction))
(provide (all-from-out hackett/prelude)
         (all-from-out hackett/private/adt)
         (all-from-out hackett/private/class)
         (except-out (all-from-out hackett/private/kernel) @%module-begin/nonconfigured)
         (all-from-out hackett/private/provide)

         (rename-out [@%module-begin #%module-begin]
                     [@%top-interaction #%top-interaction]))

(module reader syntax/module-reader hackett/main
  #:wrapper1 call-with-hackett-reading-parameterization
  (require hackett/private/reader))

; This module needs to include the configure-runtime submodule that sets up current-print, so we need
; to write it explicitly, since it won’t get created by the #%module-begin binding defined in this
; module. This is necessary, since the -I flag provided to the racket executable loads the
; configure-runtime submodule present in the specified <init-lib>, and it completely ignores the
; #%module-begin *exported* by <init-lib>.
;
; This is different from the REPL in DrRacket, which takes a different approach to initializing the
; namespace. It effectively uses the contents of the definitions window to create a module that can be
; provided to module->namespace, and it uses the configure-runtime submodule of the module in the
; definitions window, *not* the configure-runtime submodule of the #lang or module language used. This
; means that #%module-begin *is* relevant in DrRacket, which is generally the more intuitive and
; useful approach, but the top level initialization performed by the racket excutable does not create
; a fresh module (it merely requires the library into the top level namespace).

(module configure-runtime racket/base
  (require (only-in hackett/private/toplevel make-hackett-print))
  (current-print (make-hackett-print)))

(define-simple-macro (@%module-begin body ...)
  (@%module-begin/nonconfigured
   (module configure-runtime racket/base
     (require (submod hackett configure-runtime)))
   body ...))
