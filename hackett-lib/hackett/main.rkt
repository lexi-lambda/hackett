#lang hackett/private/kernel

; This module needs to be written in #lang hackett/private/kernel (or any #lang that provides
; hackett/private/kernel’s #%module-begin) so that it includes the configure-runtime submodule that
; sets up current-print. This is necessary, since the -I flag provided to the racket executable loads
; the configure-runtime submodule present in the specified <init-lib>, and it completely ignores the
; #%module-begin *exported* by <init-lib>.
;
; This is different from the REPL in DrRacket, which takes a different approach to initializing the
; namespace. It effectively uses the contents of the definitions window to create a module that can be
; provided to module->namespace, and it uses the configure-runtime submodule of the module in the
; definitions window, *not* the configure-runtime submodule of the #lang or module language used. This
; means that #%module-begin *is* relevant in DrRacket, which is generally the more intuitive and
; useful approach, but the top level initialization performed by the racket excutable does not create
; a fresh module (it merely requires the library into the top level namespace).

(require (only-in racket/base all-from-out module)

         hackett/prelude
         (only-in hackett/private/adt case* case λ λ* lambda lambda* defn _)
         (only-in hackett/private/class instance)
         (except-in hackett/private/kernel λ lambda)
         hackett/private/provide)
(provide (all-from-out hackett/prelude)
         (all-from-out hackett/private/adt)
         (all-from-out hackett/private/class)
         (all-from-out hackett/private/kernel)
         (all-from-out hackett/private/provide))

(module reader syntax/module-reader hackett/main
  #:wrapper1 call-with-hackett-reading-parameterization
  (require hackett/private/reader))
