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
; load pk-core.arc and pk-util.arc.
;
; This installs some lambda forms, 'tf and 'tf*, which parse to a new
; Penknife expression type, 'pk-lambdacalc-thin-fn. When an expression
; of this type is evaluated, it's compiled into an Arc expression, and
; that Arc expression is evaluated to produce the closure. The point
; of this process is to make the resulting closure faster to call
; later on, and to give it a smaller memory footprint.
;
; Whether this optimization is generally successful has yet to be
; seen, since no other kinds of Penknife lambda semantics have been
; attempted.


; Declaration listing:
;
; pk-nometa*                      ; value of type 'pk-ad-hoc-meta
; (pk-env-shadow-sobj env binds)
; (pk-copy-hyperenv hyperenv)
; (pk-hyperenv-shadow-assoclist hyperenv binds)
;
; pk-local-limit-env*  ; value of type 'pk-local-limit-env
;
; (pk-staticenv-default-op-parser self)        ; external rulebook
; (pk-dynenv-shadows self varname)             ; external rulebook
; (pk-staticenv-read-parse-tl self lexid str)  ; external rulebook
; (pk-dynenv-ensure-binding self varname)      ; external rulebook
; (pk-dynenv-get-binding self varname)         ; external rulebook
; (pk-dynenv-get self varname)                 ; external rulebook
; (pk-dynenv-get-meta self varname)            ; external rulebook
; (pk-dynenv-set varname self new-value)       ; external rulebook
; (pk-dynenv-set-meta self varname new-value)  ; external rulebook
;
; (pk-mangle hyped-sym)
;
; (pk-captures-hyperenv self)  ; rulebook
;
; (odedup self (o test missing))  ; rulebook
;
; (def-pk-optimize-subexpr type . body)       ; macro
; (def-pk-optimize-subexpr-meta type . body)  ; macro
; (pk-optimize-subexpr self lexid dyn-hyperenv local-lex env-lex)
;   ; rulebook
; (pk-optimize-subexpr-meta self lexid dyn-hyperenv local-lex env-lex)
;   ; rulebook
;
; < some external rules using 'def-pk-eval >
;
; (pk-finish-fn args rest body lexid static-hyperenv)
; (pk-thin-fn-rest-parser op-fork body lexid static-hyperenv)
; (pk-thin-fn-parser op-fork body lexid static-hyperenv)
;
; Penknife  [tf [args$&] body&]            ; syntax
; Penknife  [tf* [args$&] restarg$ body&]  ; syntax
;
;
; Type listing:
;
; pk-shadowed-env
;   rep: A list which supports the following fields:
;   rep._.0:  A table mapping variable names (symbols) to singleton
;             lists containing their local bindings. The bindings may
;             be mutated, but this table should not be.
;   rep._.1:  A parent environment, which should be used in order to
;             deal with everything except looking up the local
;             bindings we keep here.
;
; pk-local-limit-env
;   rep: Ignored. This value represents an environment that doesn't do
;        anything on its own. Instead, operations on it are supposed
;        to trickle down through the other environments in the
;        hyperenvironment according to 'pk-hyperenv-traverse.
;
; pk-lambdacalc-thin-fn
;   rep: A list which supports the following fields:
;   rep._.0:  A proper list of hyped symbols representing the non-rest
;             parameters of this lambda form.
;   rep._.1:  If non-nil, a singleton proper list containing a hyped
;             symbol representing the rest parameter of this lambda
;             form.
;   rep._.2:  A proper list of the expressions comprising the body of
;             this lambda form, where each expression is a value of
;             one of the 'pk-lambdacalc-[something] types.


; TODO: See if 'pk-shadowed-env can be implemented in such a way that
; it doesn't end up keeping a hard reference to shadowed bindings.


(= pk-nometa* (pk-meta))

(def pk-env-shadow-sobj (env binds)
  (annotate 'pk-shadowed-env
    (list (listtab:ut:maplet (varname (meta)) tablist.binds
            (list varname (list pk-make-ad-hoc-binding-meta.meta)))
          env)))

(def pk-copy-hyperenv (hyperenv)
  (annotate 'pk-hyperenv (copy rep.hyperenv)))

(def pk-hyperenv-shadow-assoclist (hyperenv binds)
  (ut:ret new-hyperenv pk-copy-hyperenv.hyperenv
    (let binds-sobjs (table)
      (each (hyped-sym meta) binds
        (let (name . lexid) rep.hyped-sym
          (or= rep.new-hyperenv.lexid
                 (list pk-local-limit-env* pk-local-limit-env*))
          (= (.name:or= do.binds-sobjs.lexid (table)) list.meta)))
      (each (lexid (env)) rep.new-hyperenv
        (= rep.new-hyperenv.lexid
             (list:pk-env-shadow-sobj env
               (or do.binds-sobjs.lexid (table))))))))


(= pk-local-limit-env* (annotate 'pk-local-limit-env nil))


(rc:ontype pk-staticenv-default-op-parser ()
             pk-shadowed-env pk-shadowed-env
  (pk-staticenv-default-op-parser rep.self.1))

(rc:ontype pk-staticenv-default-op-parser ()
             pk-local-limit-env pk-local-limit-env
  nil)

(rc:ontype pk-dynenv-shadows (varname)
             pk-shadowed-env pk-shadowed-env
  (if rep.self.0.varname t (pk-dynenv-shadows rep.self.1 varname)))

(rc:ontype pk-dynenv-shadows (varname)
             pk-local-limit-env pk-local-limit-env
  nil)

(rc:ontype pk-staticenv-read-parse-tl (lexid str)
             pk-shadowed-env pk-shadowed-env
  (pk-staticenv-read-parse-tl rep.self.1 lexid str))

(rc:ontype pk-staticenv-read-parse-tl (lexid str)
             pk-local-limit-env pk-local-limit-env
  (err "A 'pk-local-limit-env value can't read-parse-tl."))

(rc:ontype pk-dynenv-ensure-binding (varname)
             pk-shadowed-env pk-shadowed-env
  (aif rep.self.0.varname
    car.it
    (pk-dynenv-ensure-binding rep.self.1 varname)))

(rc:ontype pk-dynenv-ensure-binding (varname)
             pk-local-limit-env pk-local-limit-env
  (err "A 'pk-local-limit-env value can't ensure-binding."))

(rc:ontype pk-dynenv-get-binding (varname)
             pk-shadowed-env pk-shadowed-env
  (or rep.self.0.varname (pk-dynenv-get-binding rep.self.1 varname)))

(rc:ontype pk-dynenv-get-binding (varname)
             pk-local-limit-env pk-local-limit-env
  nil)

(rc:ontype pk-dynenv-get (varname) pk-shadowed-env pk-shadowed-env
  (pk-binding-get:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-get (varname)
             pk-local-limit-env pk-local-limit-env
  (pk-binding-get:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-get-meta (varname)
             pk-shadowed-env pk-shadowed-env
  (pk-binding-get-meta:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-get-meta (varname)
             pk-local-limit-env pk-local-limit-env
  (pk-binding-get-meta:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-set (varname new-value)
             pk-shadowed-env pk-shadowed-env
  (pk-binding-set (pk-dynenv-ensure-binding self varname) new-value))

(rc:ontype pk-dynenv-set (varname new-value)
             pk-local-limit-env pk-local-limit-env
  (pk-binding-set (pk-dynenv-ensure-binding self varname) new-value))

(rc:ontype pk-dynenv-set-meta (varname new-value)
             pk-shadowed-env pk-shadowed-env
  (pk-binding-set-meta
    (pk-dynenv-ensure-binding self varname) new-value))

(rc:ontype pk-dynenv-set-meta (varname new-value)
             pk-local-limit-env pk-local-limit-env
  (pk-binding-set-meta
    (pk-dynenv-ensure-binding self varname) new-value))


; Pick an unlikely-to-write name without being too obscure and without
; accidentally using ssyntax (even custom ssyntax hacked onto Arc,
; within reason).
(def pk-mangle (hyped-sym)
  (let mangle-sym
         (fn (name)
           (tostring:w/instring s (string:or name "nil")
             ; NOTE: Jarc's readc returns the character equivalent of
             ; -1 on EOF.
             (whilet char (check readc.s [and _ (~is int._ -1)])
               (if (or letter.char digit.char)
                 writec.char
                   (is char #\-)
                 (pr "--")
                 (pr "-u" (coerce int.char 'string 16) "-")))))
    (sym:+ "pk--" (treewise (fn (a b)
                              (sym:string "-s-" a "-i-" b "-e-"))
                    mangle-sym rep.hyped-sym))))


(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call pk-lambdacalc-call
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call-set pk-lambdacalc-call-set
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-literal pk-lambdacalc-literal
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-literal-meta pk-lambdacalc-literal-meta
  nil)

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-var pk-lambdacalc-var
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  nil)

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-set pk-lambdacalc-set
  (pk-captures-hyperenv rep.self.1))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  (pk-captures-hyperenv rep.self.1))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-demeta pk-lambdacalc-demeta
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-thin-fn pk-lambdacalc-thin-fn
  (some pk-captures-hyperenv rep.self.2))


; NOTE: Rainbow's profiler doesn't like function calls in optional
; arguments.
(w/uniq missing
  (rc:ontype odedup ((o test missing)) rc.list list
    (when (is test missing)
      (= test rc.oiso2))
    (rev:ut:ret acc nil
      (each elem self
        (unless (some [do.test elem _] acc)
          (push elem acc))))))


(mac def-pk-optimize-subexpr (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv
                             local-lex env-lex fail)
                          ,@body)
       (,rc!ontype pk-optimize-subexpr
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                        env-lex fail))
       (,rc!ontype pk-optimize-subexpr-meta
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         `(pk-meta result
            ,(,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                            env-lex fail))))))

(mac def-pk-optimize-subexpr-meta (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv
                             local-lex env-lex fail)
                          ,@body)
       (,rc!ontype pk-optimize-subexpr
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         `(pk-demeta ,(,g-backing-fn rep.self self lexid dyn-hyperenv
                                     local-lex env-lex fail)))
       (,rc!ontype pk-optimize-subexpr-meta
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                        env-lex fail)))))

(def-pk-optimize-subexpr pk-lambdacalc-call
  `(pk-call
     ,@(map [pk-optimize-subexpr
              _ lexid dyn-hyperenv local-lex env-lex]
            self)))

(def-pk-optimize-subexpr pk-lambdacalc-call-set
  `(pk-call-set
     ,@(map [pk-optimize-subexpr
              _ lexid dyn-hyperenv local-lex env-lex]
            self)))

(def-pk-optimize-subexpr-meta pk-lambdacalc-call-meta
  `(pk-call-meta
     ,@(map [pk-optimize-subexpr
              _ lexid dyn-hyperenv local-lex env-lex]
            self)))

(def-pk-optimize-subexpr pk-lambdacalc-literal
  (zap car self)
  `(',thunk.self))

(def-pk-optimize-subexpr-meta pk-lambdacalc-literal-meta
  (zap car self)
  `(',thunk.self))

; NOTE: In the following rules, we wrap the bindings we get in thunks
; so that their identities are preserved in official Arc 3.1 and
; Anarki. If we just included the binding directly in the quote, using
; "',binding", then (assuming the binding is an Arc tagged value,
; which is a Racket vector) Racket would evaluate the quoted vector by
; copying it.

(def-pk-optimize-subexpr pk-lambdacalc-var
  (if (oi.opos local-lex self)
    `(pk-demeta ,pk-mangle.self)
      (oi.opos env-lex self)
    `(pk-dyn-hyperenv-get _ (',thunk.self))
    (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv self)
      `(pk-binding-get (',thunk.binding)))))

(def-pk-optimize-subexpr-meta pk-lambdacalc-var-meta
  (if (oi.opos local-lex self)
    pk-mangle.self
      (oi.opos env-lex self)
    `(pk-dyn-hyperenv-get-meta _ (',thunk.self))
    (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv self)
      `(pk-binding-get-meta (',thunk.binding)))))

(def-pk-optimize-subexpr pk-lambdacalc-set
  (withs ((var val-expr) self
          val (pk-optimize-subexpr
                val-expr lexid dyn-hyperenv local-lex env-lex))
    (if (oi.opos local-lex var)
      `(assign ,pk-mangle.var (pk-meta result ,val))
        (oi.opos env-lex var)
      `(pk-dyn-hyperenv-set _ (',thunk.var) ,val)
      (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv var)
        `(pk-binding-set (',thunk.binding) ,val)))))

(def-pk-optimize-subexpr pk-lambdacalc-set-meta
  (withs ((var val-expr) self
          val (pk-optimize-subexpr
                val-expr lexid dyn-hyperenv local-lex env-lex))
    (if (oi.opos local-lex var)
      `(assign ,pk-mangle.var ,val)
        (oi.opos env-lex var)
      `(pk-dyn-hyperenv-set-meta _ (',thunk.var) ,val)
      (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv var)
        `(pk-binding-set-meta (',thunk.binding) ,val)))))

(def-pk-optimize-subexpr pk-lambdacalc-demeta
  (pk-optimize-subexpr-meta
    car.self lexid dyn-hyperenv local-lex env-lex))

(def-pk-optimize-subexpr pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          capturing         (some pk-captures-hyperenv body)
          arg-set           (odedup:join args rest)
          inner-local-lex   (union rc.oiso2
                              local-lex (unless capturing arg-set))
          inner-env-lex     (union rc.oiso2
                              env-lex (when capturing arg-set)))
    `(fn ,(ut.join-end (map pk-mangle args)
                       (when rest (pk-mangle car.rest)))
       ,@(when rest
           (let var (pk-mangle car.rest)
             `((assign ,var (copylist ,var)))))
       ,@(map [let _ pk-mangle._ `(assign ,_ (pk-meta result ,_))]
              arg-set)
       ,@(let body
                (map [pk-optimize-subexpr _ lexid dyn-hyperenv
                                          inner-local-lex
                                          inner-env-lex]
                     body)
           (case capturing nil body
             `((let _ (pk-hyperenv-shadow-assoclist _
                        (list ,@(map [do `(list (',thunk._)
                                                ,pk-mangle._)]
                                     arg-set)))
                 ,@body)))))))


; NOTE: In an optimized expression, when the current dynamic
; hyperenvironment might be captured, it's in the variable _.
(def-pk-eval pk-lambdacalc-thin-fn
  (eval `(let _ (',thunk.dyn-hyperenv)
           ,(pk-optimize-subexpr
              tagged-self lexid dyn-hyperenv nil nil))))


(def pk-finish-fn (args rest body lexid static-hyperenv)
  (annotate 'pk-lambdacalc-thin-fn
    (list args rest (map [pk-fork-to-get:pk-parse
                           _ lexid static-hyperenv]
                         body))))

(def pk-thin-fn-rest-parser (op-fork body lexid static-hyperenv)
  (let token-args otokens.body
    (unless (<= 3 len.token-args)
      (err:+ "A thin-fn-rest body didn't have at least three words "
             "in it."))
    (withs ((args rest . body) token-args
            check
              [or _ (err "A fn-rest parameter wasn't an identifier.")]
            args (map check (pk-identifier-list args lexid))
            rest (do.check:pk-soup-identifier rest lexid))
      (pk-parse-leaf-from-thunk lexid static-hyperenv
        (thunk:pk-finish-fn args list.rest body lexid
          (pk-hyperenv-shadow-assoclist static-hyperenv
            (map [list _ pk-nometa*] (join args list.rest))))))))

(def pk-thin-fn-parser (op-fork body lexid static-hyperenv)
  (let token-args otokens.body
    (unless (<= 2 len.token-args)
      (err "A thin-fn body didn't have at least two words in it."))
    (withs ((args . body) token-args
            check [or _ (err "A fn parameter wasn't an identifier.")]
            args (map check (pk-identifier-list args lexid)))
      (pk-parse-leaf-from-thunk lexid static-hyperenv
        (thunk:pk-finish-fn args nil body lexid
          (pk-hyperenv-shadow-assoclist static-hyperenv
            (map [list _ pk-nometa*] args)))))))


(pk-dynenv-set-meta pk-replenv* 'tf pk-wrap-op.pk-thin-fn-parser)

(pk-dynenv-set-meta pk-replenv* 'tf*
  pk-wrap-op.pk-thin-fn-rest-parser)
