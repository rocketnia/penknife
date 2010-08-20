; pk-thin-fn.arc


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
; load penknife.arc.
;
; This installs some lambda forms, 'tf and 'tf*, which compile to a
; new Penknife expression type, 'pk-lambdacalc-thin-fn. When an
; expression of this type is evaluated, it's compiled into an Arc
; expression, and that Arc expression is evaluated to produce the
; closure. The point of this process is to make the resulting closure
; faster to call later on, and to give it a smaller memory footprint.
;
; Whether this optimization is generally successful has yet to be
; seen, since no other kinds of Penknife lambda semantics have been
; attempted.


; Definition listing:
;
; (pk-staticenv-shadow self vars)  ; rulebook
;
; (pk-mangle name)
;
; (pk-optimize-expr self dynenv lex)  ; rulebook
;
; (pk-thin-fn-rest-compiler compiled-op body staticenv)
; (pk-thin-fn-compiler compiled-op body staticenv)
;
;
; Type listing:
;
; pk-lambdacalc-thin-fn
;   rep: A list which supports the following fields:
;   rep._.0:  A proper list of symbols representing the non-rest
;             parameters of this lambda form.
;   rep._.1:  If non-nil, a singleton proper list containing a symbol
;             representing the rest parameter of this lambda form.
;   rep._.2:  A proper list of the expressions comprising the body of
;             this lambda form, where each expression is a value of
;             one of the 'pk-lambdacalc-[something] types.


(rc:ontype pk-staticenv-shadow (vars) pk-ad-hoc-env pk-ad-hoc-env
  (annotate 'pk-ad-hoc-env
    (apply copy rep.self (mappend [list _ nil] vars))))


(def pk-mangle (name)
  (sym:+ "pk_" (or name "nil")))


(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-call pk-lambdacalc-call
  `(pk-call ,@(map [pk-optimize-expr _ dynenv lex] rep.self)))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-call-set pk-lambdacalc-call-set
  `(pk-call-set ,@(map [pk-optimize-expr _ dynenv lex] rep.self)))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  `(pk-call-meta ,@(map [pk-optimize-expr _ dynenv lex] rep.self)))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-literal pk-lambdacalc-literal
  `',rep.self)

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-var pk-lambdacalc-var
  (zap rep self)
  (if (mem self lex)
    `((rep ,pk-mangle.self) 'result)
    (aif (pk-dynenv-get-binding dynenv self)
      `(pk-binding-get ',car.it)
      `(pk-dynenv-get ',dynenv ',self))))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  (zap rep self)
  (if (mem self lex)
    pk-mangle.self
    (aif (pk-dynenv-get-binding dynenv self)
      `(pk-binding-get-meta ',car.it)
      `(pk-dynenv-get-meta ',dynenv ',self))))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-set pk-lambdacalc-set
  (withs ((var val-expr)  rep.self
          val             (pk-optimize-expr val dynenv lex))
    (if (mem var lex)
      `(assign ,pk-mangle.var (pk-meta result ,val))
      (aif (pk-dynenv-get-binding dynenv var)
        `(pk-binding-set ',car.it ,val)
        `(pk-dynenv-set ',dynenv ',var ,val)))))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  (withs ((var val-expr)  rep.self
          val             (pk-optimize-expr val dynenv lex))
    (if (mem var lex)
      `(assign ,pk-mangle.var ,val)
      (aif (pk-dynenv-get-binding dynenv var)
        `(pk-binding-set-meta ',car.it ,val)
        `(pk-dynenv-set-meta ',dynenv ',var ,val)))))

(rc:ontype pk-optimize-expr (dynenv lex)
             pk-lambdacalc-thin-fn pk-lambdacalc-thin-fn
  (withs ((args rest body)  rep.self
          arg-set           (dedup:join args rest)
          innerlex          (union is arg-set lex))
    `(fn ,(ut.join-end (map pk-mangle args)
                       (when rest (pk-mangle car.rest)))
       ,@(when rest
           (let var (pk-mangle car.rest)
             `((assign ,var (annotate 'pk-linklist
                              (copylist ,var))))))
       ,@(map [let _ pk-mangle._ `(assign ,_ (pk-meta result ,_))]
              arg-set)
       ,@(map [pk-optimize-expr _ dynenv innerlex] body))))


(def-pk-eval pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          arg-set           (dedup:join args rest))
    (eval `(let env ',dynenv
             (fn ,(ut.join-end (map pk-mangle args)
                               (when rest (pk-mangle car.rest)))
               ,@(when rest
                   (let var (pk-mangle car.rest)
                     `((assign ,var (annotate 'pk-linklist
                                      (copylist ,var))))))
               ,@(map [let _ pk-mangle._
                        `(assign ,_ (pk-meta result ,_))]
                      arg-set)
               ,@(map [pk-optimize-expr _ dynenv arg-set]
                      body))))))


(def pk-thin-fn-rest-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (<= 3 len.token-args)
      (err:+ "A thin-fn-rest body didn't have at least three words "
             "in it."))
    (let (args rest . body) token-args
      (unless (and (single rep.args)
                   (single rep.args.0)
                   (isa rep.args.0.0 'pk-bracketed-soup))
        (err:+ "A thin-fn-rest parameter list wasn't a "
               "'pk-bracketed-soup."))
      (zap otokens:rep:caar:rep args)
      (unless (all pk-soup-identifier (cons rest args))
        (err "A thin-fn-rest parameter wasn't an identifier."))
      (pk-compile-leaf-from-thunk staticenv
        (thunk:let innerenv (pk-staticenv-shadow staticenv
                              (cons (zap sym:car:rep rest)
                                    (zap [map sym:car:rep _] args)))
          (annotate 'pk-lambdacalc-thin-fn
            (list args list.rest
              (map [pk-call:!get:rep:pk-soup-compile _ innerenv]
                   body))))))))

(def pk-thin-fn-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (<= 2 len.token-args)
      (err "A thin-fn body didn't have at least two words in it."))
    (let (args . body)  token-args
      (unless (and (single rep.args)
                   (single rep.args.0)
                   (isa rep.args.0.0 'pk-bracketed-soup))
        (err "A thin-fn parameter list wasn't a 'pk-bracketed-soup."))
      (zap otokens:rep:caar:rep args)
      (unless (all pk-soup-identifier args)
        (err "A thin-fn parameter wasn't an identifier."))
      (zap [map sym:car:rep _] args)
      (pk-compile-leaf-from-thunk staticenv
        (thunk:let innerenv (pk-staticenv-shadow staticenv args)
          (annotate 'pk-lambdacalc-thin-fn
            (list args nil
              (map [pk-call:!get:rep:pk-soup-compile _ innerenv]
                   body))))))))


(pk-dynenv-set-meta pk-replenv* 'tf
  (pk-meta compile-fork (list:pk-compile-fork-from-op
                          pk-thin-fn-compiler)))

(pk-dynenv-set-meta pk-replenv* 'tf*
  (pk-meta compile-fork (list:pk-compile-fork-from-op
                          pk-thin-fn-rest-compiler)))
