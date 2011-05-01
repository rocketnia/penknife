; Penknife core stuff.
;
; TODO: Document these Arc types:
;   pk-wrapped
;
; TODO: Document these Penknife types:
;   t-type
;   t-fn
;   t-rulebook
;   t-binding
;   t-cons
;   t-nil
;   t-core-string
;   t-unbound-error
;   t-native-error
;   t-stray-failure-error
;   t-raised-failure-error
;   t-cannot-fail-error
;   t-fn-failure
;   t-too-few-args-failure
;   t-too-many-args-failure
;   t-rulebook-failure
;   t-rb-core-call/arc-fn-failure
;   t-add-rule/rulebook-failure
;   t-unwrap-failure
;
; TODO: Finish the language!
;;;;;;;;;;----------;;;;;;;;;;----------;;;;;;;;;;----------;;;;;;;;;;


(let lathe [+ lathe-dir* _ '.arc]
  (use-fromwds-as ut do.lathe!utils
                  dy do.lathe!dyn))


wipe.pk-core-setup-bindings-needed*
wipe.pk-core-setup-steps*

(= pk-core-prefix* ut.niceuniq!core-)

(def pk-wrap (type (o unwrapped))
  (annotate 'pk-wrapped (list type unwrapped)))

; TODO: See where Penknife's "unwrap" would be more appropriate to use
; than this. This deep into the core, it usually isn't possible
; (without infinite loops), but maybe there's somewhere it is.
(def pk-ish (type x)
  (and (isa x 'pk-wrapped) (is rep.x.0 type)))

(def pk-rep (wrapped)
  rep.wrapped.1)

(= pk-t-type* pk-wrap.nil rep.pk-t-type*.0 pk-t-type*)

(def pk-type ((o info))
  (pk-wrap pk-t-type* info))

(= pk-t-unbound-error* pk-type!t-unbound-error)

(= pk-t-binding* pk-type!t-unbound-error)

(def pk-make-binding ()
  (pk-wrap pk-t-binding* (list nil nil)))

(def pk-built-in-binding-get (binding)
  (let (bound val) pk-rep.binding
    (unless bound (pk-throw:pk-wrap pk-t-unbound-error* binding))
    val))

(def pk-built-in-binding-set (binding val)
  (= pk-rep.binding.0 t pk-rep.binding.1 val))

wipe.pk-core-setup-compiled*
wipe.pk-core-setup-valid*
(def pk-core-setup ()
  (until pk-core-setup-valid*
    (= pk-core-setup-valid* t)
    wipe.pk-core-setup-compiled*  ; Release memory. :-p
    (= pk-core-setup-compiled*
      (eval:w/uniq g-core
        `(thunk:w/table ,g-core
           (with ,(ut:mappendlet _ pk-core-setup-bindings-needed*
                    `(,(sym:string pk-core-prefix* _)
                      (car:or= (,g-core ',_) (list:pk-make-binding))))
             ,@rev.pk-core-setup-steps*)))))
  call.pk-core-setup-compiled*)

(mac pkcb (var)
  (case type.var sym nil (err "Can't 'pkcb a non-symbol."))
  (unless (mem var pk-core-setup-bindings-needed*)
    (push var pk-core-setup-bindings-needed*)
    wipe.pk-core-setup-valid*)
  (sym:string pk-core-prefix* var))

(def pk-list (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
              . args)
  (ut:xloop args args
    (iflet (first . rest) args
      (pk-wrap (pk-binding-get
                   b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                 pk-binding-get-failure.b-rf b-tc)
               (list first do.next.rest))
      (pk-wrap:pk-binding-get
          b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
        pk-binding-get-failure.b-rf b-tc))))

(mac pkc-list args
  `(pk-list pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
            pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
            pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil ,@args))

(mac pkc-arc-to-list (arc-list)
  `(apply pk-list
     pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
     pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
     pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil ,arc-list))

; The final argument is assumed to be a Penknife sequence already. In
; particular, if it's Arc nil, that value will be interpreted as
; Penknife f, not Penknife nil, and it will cause an error when
; iterating the sequence.
(def pk-list* (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
               first . rest)
  (ut:xloop first first args args
    (iflet (second . rest) rest
      (pk-wrap (pk-binding-get
                   b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                 pk-binding-get-failure.b-rf b-tc)
               (list first (do.next second rest)))
      first)))

(mac pkc-list* args
  `(pk-list* pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
             pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
             pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil
     ,@args))

(mac pkc-arc-to-list* (arc-list)
  `(apply pk-list*
     pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
     pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
     pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil ,arc-list))

(mac pk-failcall (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                  func fail . args)
  (pk-core-call b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
    pk-binding-get-failure.b-rf func fail
   (apply pk-list b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
     args)))

(mac pk-failcall* (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                   func fail . args)
  (pk-core-call b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
    pk-binding-get-failure.b-rf func fail
   (apply pk-list* b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
     args)))

(mac pkc-failcall (func fail . args)
  `(pk-failcall pkcb.rb-binding-get pkcb.rb-core-call
     pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
     pkcb.t-rulebook-failure pkcb.t-stray-failure-error
     pkcb.t-cons pkcb.t-nil ,func ,fail ,@args))

; The final argument is assumed to be a Penknife sequence already. See
; the definition of 'pk-list*.
(mac pkc-failcall* (func fail . args)
  `(pk-failcall* pkcb.rb-binding-get pkcb.rb-core-call
     pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
     pkcb.t-rulebook-failure pkcb.t-stray-failure-error
     pkcb.t-cons pkcb.t-nil ,func ,fail ,@args))

; The final argument is assumed to be a Penknife sequence already. See
; the definition of 'pk-list*.
(mac pkc-call* (func . args)
  `(pkc-failcall*
     ,func (pk-binding-get-failure pkcb.raise-failure) ,@args))

(mac pkc-call (func . args)
  `(pkc-failcall
     ,func (pk-binding-get-failure pkcb.raise-failure) ,@args))

(mac pkc (expr)
  (case type.expr
    sym   `(pk-built-in-binding-get:pkcb ,expr)
    cons  `(pkc-call (pkc ,car.expr) ,@cdr.expr)
          (err "Can't 'pkc a non-symbol, non-cons.")))

(mac pkc-wrap (type (o unwrapped))
  `(pk-wrap (pkc ,type) ,unwrapped))

(mac named (name . body)
  `(let ,name nil
     (= ,name (do ,@body))))

; b-rbg    = binding for rb-binding-get
; b-rcc    = binding for rb-core-call
; b-rf     = binding for raise-failure
; b-tf     = binding for t-fn
; b-tr     = binding for t-rulebook
; b-trf    = binding for t-rulebook-failure
; b-tsfe   = binding for t-stray-failure-error
; b-tc     = binding for t-cons
; b-tn     = binding for t-nil
; b-ri     = binding for rb-ifdecap
; b-ttfaf  = binding for t-too-few-args-failure
; b-ttmaf  = binding for t-too-many-args-failure
; b-tff    = binding for t-fn-failure
(mac pk-failfn (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn b-ri
                b-ttfaf b-ttmaf b-tff fail parms . body)
  (w/uniq (gb-rbg gb-rcc gb-rf gb-tf gb-tr gb-trf gb-tsfe gb-tc gb-tn
           gb-ri gb-ttfaf gb-ttmaf gb-tff
           g-self g-fail g-args g-failfail g-failargs g-first)
    (withs (rf `(pk-binding-get-failure ,gb-rf)
            binding-get [do `(pk-binding-get
                                 ,gb-rbg ,gb-rcc ,gb-rf ,gb-tf ,gb-tr
                                 ,gb-trf ,gb-tsfe ,gb-tc ,gb-tn
                               ,rf ,_)])
      `(with (,gb-rbg ,b-rbg ,gb-rcc ,b-rcc ,gb-rf ,b-rf ,gb-tf ,b-tf
              ,gb-tr ,b-tr ,gb-trf ,b-trf ,gb-tsfe ,g-tsfe
              ,gb-tc ,b-tc ,gb-tn ,b-tn ,gb-ri ,b-ri
              ,gb-ttfaf ,b-ttfaf ,gb-ttmaf ,b-ttmaf ,gb-tff ,b-tff)
         (named ,g-self
           (pk-wrap ,do.binding-get.gb-tf
             (fn (,g-fail ,g-args)
               (let ,g-fail
                      (pk-wrap ,do.binding-get.gb-tf
                        (fn (,g-failfail ,g-failargs)
                          (pk-failcall ,gb-rbg ,gb-rcc ,gb-rf ,gb-tf
                              ,gb-tr ,gb-trf ,gb-tsfe ,gb-tc ,gb-tn
                            ,g-fail ,g-failfail
                            (pk-wrap ,do.binding-get.gb-tff
                              (list ,g-self ',fail ',parms
                                ,g-args ,g-failargs)))))
                 ,(ut:xloop theseparms parms
                    (if acons.theseparms
                      `(fn-pk-ifdecap-arc ,gb-rbg ,gb-rcc ,gb-rf
                           ,gb-tf ,gb-tr ,gb-trf ,gb-tsfe ,gb-tc
                           ,gb-tn ,gb-ri ,gb-ttfaf ,gb-ttmaf ,gb-tff
                           ,g-fail ,g-args
                         (fn (,g-first ,g-args)
                           (let ,car.theseparms ,g-first
                             ,(do.next cdr.theseparms)))
                         (thunk:pk-failcall
                             ,gb-rbg ,gb-rcc ,gb-rf ,gb-tf ,gb-tr
                             ,gb-trf ,gb-tsfe ,gb-tc ,gb-tn
                           ,g-fail ,rf ,do.binding-get.gb-ttfaf))
                        theseparms
                      `(with (,theseparms ,g-args ,fail ,g-fail)
                         ,@body)
                      `(fn-pk-ifdecap-arc ,gb-rbg ,gb-rcc ,gb-rf
                           ,gb-tf ,gb-tr ,gb-trf ,gb-tsfe ,gb-tc
                           ,gb-tn ,gb-ri ,gb-ttfaf ,gb-ttmaf ,gb-tff
                           ,g-fail ,g-args
                         (fn (,g-first ,g-args)
                           (pk-failcall ,gb-rbg ,gb-rcc ,gb-rf ,gb-tf
                               ,gb-tr ,gb-trf ,gb-tsfe ,gb-tc ,gb-tn
                             ,g-fail ,rf ,do.binding-get.gb-ttmaf))
                         (thunk:let ,fail ,g-fail
                           ,@body))))))))))))

(mac pkc-failfn (fail parms . body)
  `(pk-failfn pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
     pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
     pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil pkcb.rb-ifdecap
     pkcb.t-too-few-args-failure pkcb.t-too-many-args-failure
     pkcb.t-fn-failure
     ,fail ,parms ,@body))

(mac pkc-fn (parms . body)
  `(pkc-failfn nil ,parms ,@body))

(def fn-pk-ifdecap (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                    b-ri fail self arc-then arc-else pk-then pk-else)
  (withs (rf (fn () pk-binding-get-failure.b-rf)
          binding-get [pk-binding-get b-rbg b-rcc b-rf b-tf b-tr b-trf
                                     b-tsfe b-tc b-tn
                        call.rf _])
    (if (pk-ish do.binding-get.b-tc self)
      (do.arc-then pk-rep.self.0 pk-rep.self.1)
        (pk-ish do.binding-get.b-tn self)
      call.arc-else
      (pk-failcall b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
        (pk-binding-get
            b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
          call.rf b-ri)
        fail self pk-then pk-else))))

(def fn-pk-ifdecap-arc (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe
                        b-tc b-tn b-ri b-ttfaf b-ttmaf b-tff
                        fail self then else)
  (fn-pk-ifdecap
      b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn b-ri
    fail self then else
    (pk-failfn b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn b-ri
               b-ttfaf b-ttmaf b-tff
      fail (first rest) (do.then first rest))
    (pk-failfn b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn b-ri
               b-ttfaf b-ttmaf b-tff
      fail () call.else)))

(mac pkc-ifdecap (fail first rest self then . elses)
  `(fn-pk-ifdecap-arc pkcb.rb-binding-get pkcb.rb-core-call
     pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
     pkcb.t-rulebook-failure pkcb.t-stray-failure-error
     pkcb.t-cons pkcb.t-nil pkcb.rb-ifdecap
     pkcb.t-too-few-args-failure pkcb.t-too-many-args-failure
     pkcb.t-fn-failure
     ,fail ,self (fn (,first ,rest) ,then) (fn () ,@elses)))


(mac pk-core-step body
  `(push '(do ,@body) pk-core-setup-steps*))

(mac pk-core-def (name val)
  `(pk-core-step:pk-built-in-binding-set (pkcb ,name) ,val))

(mac pk-core-fun (name parms . body)
  `(pk-core-def ,name (pkc-failfn fail ,parms ,@body)))

(mac pk-core-rulebook (name)
  `(pk-core-def ,name (pk-make-rulebook pkc.t-rulebook
                        (pkc-wrap t-core-string ',name))))

(mac pk-core-rule (rulebook-name parms name . body)
  (w/uniq (g-fail g-args)
    `(do (pk-core-fun ,name ,parms ,@body)
         (pk-core-step:pk-built-in-add-rule (pkc ,rulebook-name)
           (pkc-failfn ,g-fail ,g-args
             (pkc-failcall* (pkc ,name) ,g-fail ,g-args))
           (list ',name ',parms)))))

(mac pk-core-type (name)
  `(pk-core-def ,name (pk-type ',name)))


(= pk-throw-param* (dy.make-param
                     [err:if (pk-ish pk-t-native-error* _)
                       (error-message rep._.1)
                       (tostring write._)]))

(def fn-pk-ifexception (main then else)
  (let (exception result)
         (catch:dy:param-let pk-throw-param* [throw:list t _]
           (list nil call.main))
    (.result:if exception then else)))

(mac pk-ifexception (exception success main then . elses)
  `(fn-pk-ifexception (fn () ,main) (fn (,exception) ,then)
                                    (fn (,success) (if ,@elses))))

(mac pk-itifexception (main then . elses)
  `(pk-ifexception it it ,main ,then ,@elses))

(def pk-throw (exception)
  dy.param-get.pk-throw-param*.exception)


(def pk-list-to-arc (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-ri
                     b-ttfaf b-ttmaf b-tff
                     fail lst)
  (fn-pk-ifdecap-arc b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                     b-ri b-ttfaf b-ttmaf b-tff
    fail lst
    (fn (first rest)
      (cons first (pk-list-to-arc b-rbg b-rcc b-rf b-tf b-tr b-trf
                    b-tsfe b-ri b-ttfaf b-ttmaf b-tff fail rest)))
    thunk.nil))

(def pkc-list-to-arc (lst)
  `(pk-list-to-arc pkcb.rb-binding-get pkcb.rb-core-call
       pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
       pkcb.t-rulebook-failure pkcb.t-stray-failure-error
       pkcb.t-rb-ifdecap pkcb.t-too-few-args-failure
       pkcb.t-too-many-args-failure pkcb.t-fn-failure
     pkc.raise-failure ,lst))


(def pk-make-rulebook (t-rulebook (o info))
  (pk-wrap t-rulebook (list info nil)))

(def pk-built-in-add-rule (rulebook rule (o rule-info))
  (push (list rule-info rule) pk-rep.rulebook.1))


(def fn-w/escape-fail (inner-fail b-rbg b-rcc b-rf b-tf b-tr b-trf
                       b-tsfe b-tc b-tn body)
  (withs (call-token list.nil
          rf (fn () pk-binding-get-failure.b-rf)
          tsfe (thunk:pk-binding-get
                   b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                 call.rf b-tsfe))
    (after
      (pk-itifexception
          (do.body [pk-throw:pk-wrap call.tsfe (list call-token _)])
        (if (and (pk-ish call.tsfe it) (is call-token pk-rep.it.0))
          (pk-core-call
              b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
            call.rf inner-fail call.rf pk-rep.it.1)
          pk-throw.it)
        it)
      ; Mark the strays as actually being stray, to help with
      ; debugging.
      (= car.call-token t))))

(mac w/escape-fail (var inner-fail b-rbg b-rcc b-rf b-tsfe b-tc b-tn
                    . body)
  `(fn-w/escape-fail ,inner-fail
       ,b-rbg ,b-rcc ,b-rf ,b-tf ,b-tr ,b-trf ,b-tsfe ,b-tc ,b-tn
     (fn (,var) ,@body)))


(def pk-core-call (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                   outer-fail self inner-fail args)
  (withs (rf (fn () pk-binding-get-failure.b-rf)
          binding-get [pk-binding-get b-rbg b-rcc b-rf b-tf b-tr b-trf
                                      b-tsfe b-tc b-tn
                        call.rf _])
    (if (pk-ish do.binding-get.b-tf self)
      (w/escape-fail escape inner-fail
          b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
        (pk-rep.self (pk-wrap do.binding-get.b-tf
                       (fn (fail args) do.escape.args))
                     args))
        (pk-ish do.binding-get.b-tr self)
      (ut:xloop rules pk-rep.self.1 rev-failures nil
        (iflet ((first-info first-rule) . rest) rules
          (pk-core-call
              b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
            call.rf first-rule
            (pk-wrap do.binding-get.b-tf
              (fn (fail args)
                (do.next rest (cons (list first-info first-rule args)
                                    rev-failures))))
            args)
          (pk-failcall
              b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
            inner-fail call.rf (pk-wrap do.binding-get.b-trf
                                 (list self rev.rev-failures)))))
      ; NOTE: This *will* cause an infinite loop if the rb-core-call
      ; binding is replaced. There may be a better design, but this is
      ; probably elegant enough.
      (pk-core-call b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
        outer-fail do.binding-get.b-rcc outer-fail
        (pk-list b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
          self inner-fail args)))))

(= pk-t-cannot-fail-error* pk-type!t-cannot-fail-error)

(def pk-binding-get-failure (b-rf)
  (if (pk-ish pk-t-binding* b-rf)
    pk-built-in-binding-get.b-rf
    (pk-throw pk-wrap.pk-t-cannot-fail-error*)))

(def pk-binding-get (b-rbg b-rbc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                     fail binding)
  (if (pk-ish pk-t-binding* binding)
    pk-built-in-binding-get.binding
    ; NOTE: This *will* cause infinite loops for several reasons.
    ; There may be a better design, but this is probably elegant
    ; enough.
    (let rf (fn () pk-binding-get-failure.b-rf)
      (pk-failcall b-rbg b-rbc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
        (pk-binding-get
            b-rbg b-rbc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
          call.rf b-rbg)
        fail binding))))


(pk-core-fun fn-ifexception (main then else)
  (let (exception result)
         (catch:dy:param-let pk-throw-param* [throw:list t _]
           (list nil pkc-call.main))
    (pkc-call (if exception then else) result)))

(pk-core-fun throw (exception)
  pk-throw.exception)

(= pk-t-native-error* pk-type!t-native-error)

(def fn-pk-arcunsafe (throw body)
  ; NOTE: Jarc 17 treats escape continuations as errors, but we don't
  ; want to translate those into Penknife exceptions, since we're
  ; using escape continuations to implement exceptions in the first
  ; place. There doesn't seem to be an obvious way to throw arbitrary
  ; JVM exceptions in Jarc, so we exploit Jarc's mistreatment of
  ; escaped continuations here in order to throw a brand new
  ; jarc.lang$Continue value that happens to be an escape continuation
  ; with the same result as the original.
  (on-err (aif jv.jclass!jarc-lang$Continue
            [if (jv.ajava _ it)
              (catch.throw jvm!value._)
              do.throw._]
            throw)
          body))

(mac pkc-arcunsafe body
  `(fn-pk-arcunsafe [pkc:throw:pk-wrap pk-t-native-error* _]
                    (fn () ,body)))


(pk-core-fun raise-failure (failure)
  (pkc:throw:pkc-wrap t-raised-failure failure))


; These are only to be used from Penknife.

(pk-core-fun fn-ifdecap (self then else)
  (fn-pk-ifdecap pkcb.rb-binding-get pkcb.rb-core-call
                 pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
                 pkcb.t-rulebook-failure pkcb.t-stray-failure-error
                 pkcb.t-cons pkcb.t-nil pkcb.rb-ifdecap
                 fail self
    (fn (first rest) (pkc-call then first rest))
    (fn () pkc-call.else)
    then
    else))

(pk-core-fun core-call (self inner-fail args)
  (pk-core-call pkcb.rb-binding-get pkcb.rb-core-call
    pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
    pkcb.t-rulebook-failure pkcb.t-stray-failure-error
    pkcb.t-cons pkcb.t-nil fail self inner-fail args))

(pk-core-fun binding-get (binding)
  (pk-binding-get pkcb.rb-binding-get pkcb.rb-core-call
    pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
    pkcb.t-rulebook-failure pkcb.t-stray-failure-error
    pkcb.t-cons pkcb.t-nil fail binding))

(pk-core-fun wrap (type unwrapped)
  (pk-wrap type unwrapped))


(= pk-fail*-param*
   (dy.make-param:fn args
     (err:+ "The call " (tostring:write:cons 'pk-fail* args) " was "
            "made outside the dynamic scope of a Penknife call to an "
            "Arc function.")))

(= pk-fail-param*
   (dy.make-param:fn args
     (err:+ "The call " (tostring:write:cons 'pk-fail args) " was "
            "made outside the dynamic scope of a Penknife call to an "
            "Arc function.")))

(def pk-fail args
  (apply dy.param-get.pk-fail-param* args))

; The final argument is assumed to be a Penknife sequence already. See
; the definition of 'pk-list*.
(def pk-fail* args
  (apply dy.param-get.pk-fail*-param* args))


(pk-core-def t-type pk-t-type*)
pk-core-type.t-fn
pk-core-type.t-rulebook
(pk-core-def t-binding pk-t-binding*)
pk-core-type.t-cons
pk-core-type.t-nil
pk-core-type.t-core-string
(pk-core-def t-unbound-error pk-t-unbound-error*)
(pk-core-def t-native-error pk-t-native-error*)
pk-core-type.t-stray-failure-error
pk-core-type.t-raised-failure-error
(pk-core-def t-cannot-fail-error pk-t-cannot-fail-error*)
pk-core-type.t-fn-failure
pk-core-type.t-too-few-args-failure
pk-core-type.t-too-many-args-failure
pk-core-type.t-rulebook-failure
pk-core-type.t-rb-core-call/arc-fn-failure
pk-core-type.t-add-rule/rulebook-failure
pk-core-type.t-unwrap-failure

(pk-core-def nil pkc-wrap.t-nil)

; TODO: See if this makes sense. Note that Penknife f will be defined
; as Arc nil in pk-util.pk. Should characters and booleans really be
; non-wrapped types?
(pk-core-def t t)


pk-core-rulebook.rb-core-call
pk-core-rulebook.add-rule
pk-core-rulebook.rb-ifdecap
pk-core-rulebook.rb-binding-get

(pk-core-rule rb-core-call (self inner-fail args) rb-core-call/arc-fn
  (case type.self fn nil
    (pkc-call fail pkc-wrap.t-rb-core-call/arc-fn-failure))
  (w/escape-fail escape inner-fail
      pkcb.rb-binding-get pkcb.rb-core-call pkcb.raise-failure
      pkcb.t-fn pkcb.t-rulebook pkcb.t-rulebook-failure
      pkcb.t-stray-failure-error pkcb.t-cons pkcb.t-nil
    (dy:param-let (pk-fail*-param*
                     (fn args (do.escape:pkc-arc-to-list* args))
                   pk-fail-param
                     (fn args (do.escape:pkc-arc-to-list args)))
      (apply self
        (pk-list-to-arc pkcb.rb-binding-get pkcb.rb-core-call
          pkcb.raise-failure pkcb.t-fn pkcb.t-rulebook
          pkcb.t-rulebook-failure pkcb.t-stray-failure-error
          pkcb.rb-ifdecap
          pkcb.t-too-few-args-failure pkcb.t-too-many-args-failure
          pkcb.t-fn-failure
          fail args)))))

(pk-core-rule add-rule (self info rule) add-rule/rulebook
  (unless (pk-ish pkc.t-rulebook self)
    (pkc-call fail pkc-wrap.t-add-rule/rulebook-failure))
  (pk-built-in-add-rule self rule info))


(pk-core-fun make-rulebook (name)
  (pk-make-rulebook pkc.t-rulebook name))

(pk-core-fun unwrap (type wrapped)
  (unless (pk-ish type wrapped)
    (pkc-call fail pkc-wrap.t-unwrap-failure))
  pk-rep.wrapped)

(pk-core-fun cons (head tail)
  (pkc-list* head tail))


;;;;;;;;;;----------;;;;;;;;;;----------;;;;;;;;;;----------;;;;;;;;;;
