#lang hackett

(provide (for-type Catch))

(type (Catch e m a) {(m a) -> {e -> (m a)} -> (m a)})
