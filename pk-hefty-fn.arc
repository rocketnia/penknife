; pk-hefty-fn.arc


; Copyright (c) 2010 Ross Angle
;
;   Permission is hereby granted, free of charge, to any person
;   obtaining a copy of this software and associated documentation
;   files (the "Software"), to deal in the Software without
;   restriction, including without limitation the rights to use, copy,
;   modify, merge, publish, distribute, sublicense, and/or sell copies
;   of the Software, and to permit persons to whom the Software is
;   furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be
;   included in all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Permission to use this software is also granted under the
; Perl Foundation's Artistic License 2.0. You may use either license,
; at your option.


; This is a plugin for Penknife. To use it, load it just after you
; load penknife.arc and pk-thin-fn.arc.
;
; This installs some lambda forms, 'hf and 'hf*, which compile to a
; new Penknife expression type, 'pk-lambdacalc-hefty-fn. When an
; expression of this type is evaluated, it's compiled into an Arc
; closure as though it's a 'pk-lambdacalc-thin-fn expression, but then
; it's packed up into a 'pk-hefty-fn value which contains the Arc
; closure, the 'pk-lambdacalc-hefty-fn expression itself, and even a
; reference to the current dynamic hyperenvironment. The point of this
; is to make it possible to serialize the closure or compile it to an
; even more efficient form.


; Declaration listing:
;
; (pk-call self . args)  ; external rule
;
; < some external rules using 'def-pk-eval >
; (pk-captures-hyperenv self)                 ; external rule
; < some external rules using 'def-pk-optimize-subexpr >
;
; (pk-hefty-fn-rest-compiler compiled-op body lexid static-hyperenv)
; (pk-hefty-fn-compiler compiled-op body lexid static-hyperenv)
;
; Penknife  [hf [args$&] body&]            ; syntax
; Penknife  [hf* [args$&] restarg$ body&]  ; syntax
;
;
; Type listing:
;
; pk-lambdacalc-hefty-fn
;   rep: A 'pk-lambdacalc-thin-fn expression.
;
; pk-hefty-fn
;   rep: A table which supports the following fields:
;   rep._!compiled:  A Penknife function representing the behavior
;                    that should happen when this object is called
;                    using 'pk-call. It's bound to be more efficient
;                    than evaluating the body directly.
;   rep._!expr:      The 'pk-lambdacalc-hefty-fn expression which
;                    returned this object.
;   rep._!hyperenv:  The dynamic hyperenvironment that existed when
;                    the 'pk-lambdacalc-hefty-fn expression was
;                    evaluated to return this object.


(rc:ontype pk-call args pk-hefty-fn pk-hefty-fn
  (apply pk-call rep.self!compiled args))


(def-pk-eval pk-lambdacalc-hefty-fn
  (annotate 'pk-hefty-fn
    (obj compiled  (pk-eval self lexid dyn-hyperenv)
         expr      tagged-self
         hyperenv  dyn-hyperenv)))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-hefty-fn pk-lambdacalc-hefty-fn
  t)

(def-pk-optimize-subexpr pk-lambdacalc-hefty-fn
  `(annotate 'pk-hefty-fn
     (obj compiled  ,(pk-optimize-subexpr
                       self lexid dyn-hyperenv local-lex env-lex)
          expr      (',thunk.tagged-self)
          hyperenv  _)))


(def pk-hefty-fn-rest-compiler
       (compiled-op body lexid static-hyperenv)
  (pk-compile-leaf-from-thunk (pk-hyperenv-get static-hyperenv lexid)
    (thunk:pk-attach:annotate 'pk-lambdacalc-hefty-fn
      (pk-detach:pk-fork-to-get:pk-thin-fn-rest-compiler
        compiled-op body lexid static-hyperenv))))

(def pk-hefty-fn-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-leaf-from-thunk (pk-hyperenv-get static-hyperenv lexid)
    (thunk:pk-attach:annotate 'pk-lambdacalc-hefty-fn
      (pk-detach:pk-fork-to-get:pk-thin-fn-compiler
        compiled-op body lexid static-hyperenv))))


(pk-dynenv-set-meta pk-replenv* 'hf pk-wrap-op.pk-hefty-fn-compiler)

(pk-dynenv-set-meta pk-replenv* 'hf*
  pk-wrap-op.pk-hefty-fn-rest-compiler)
