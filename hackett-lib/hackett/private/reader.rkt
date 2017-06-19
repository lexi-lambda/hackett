#lang racket/base

(require racket/match)

(provide call-with-hackett-reading-parameterization)

; This predicate detects the set of characters that the default Racket readtable considers to be
; delimiters, according to section 1.3.1 Delimiters and Dispatch of The Racket Reference.
(define (char-delimiter? x)
  (and (char? x)
       (or (char-whitespace? x)
           (ormap (λ (c) (char=? x c))
                  (list #\( #\) #\[ #\] #\{ #\} #\" #\, #\' #\` #\;)))))

; In order to determine if a character counts as a delimiter in the current readtable, we can use
; readtable-mapping. If it is mapped to a character in the default readtable, we just use
; char-delimiter? to check if that character is a delimiter. We also need to check if it is bound to a
; 'terminating-macro, which should also be treated as a delimiter.
(define (readtable-mapping-delimiter? x)
  (match/values (readtable-mapping (current-readtable) x)
    [[(? char-delimiter?) #f _] #t]
    [['terminating-macro  _  _] #t]
    [[_                   _  _] #f]))

; Extends a readtable to make the bare use of ‘.’ a valid symbol.
(define (make-dot-readtable readtable)
  (define read-dot
    (case-lambda
      [(c in srcname line col pos)
       (if (readtable-mapping-delimiter? (peek-char in))
           (datum->syntax #f '|.| (list srcname line col pos 1) #'original)
           (read-syntax/recursive srcname in c readtable))]
      [(c in)
       (if (readtable-mapping-delimiter? (peek-char in))
           '|.|
           (read/recursive in c readtable))]))
  (make-readtable readtable #\. 'non-terminating-macro read-dot))

(define (call-with-hackett-reading-parameterization proc)
  (parameterize ([read-accept-dot #f]
                 [read-accept-infix-dot #f]
                 [read-accept-bar-quote #f]
                 [current-readtable (make-dot-readtable (current-readtable))])
    (proc)))
