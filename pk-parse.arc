; Penknife parser stuff.
;
; This depends on the following non-core Penknife utilities:
;
; defined in "core environment stuff": hyperenv-get-var-expression
;
; defined in "AST stuff": express-form express-calculation
;
; TODO: Document the following Penknife types:
;   Arc's t
;   Arc's nil
;   Arc's characters
;   t-core-text
;   t-core-sip-hype
;   t-hyped-sym
;   t-white
;   t-core-sip-brackets


(mac pkc-relycall (func . args)
  `(pkc-failcall ,func fail ,@args))

(mac pkc-relycall* (func . args)
  `(pkc-failcall* ,func fail ,@args))

(mac pkc-ifsuccess (success failure (func . args) then . else)
  (w/uniq g-fail
    `(pkc-failcall (pkc-failfn ,g-fail ()
                     (let ,success (pkc-failcall ,func ,g-fail ,@args)
                       ,then))
                   (pkc-fn (,failure) ,@else))))

(mac pkc-ifsuccess* (success failure (func . args) then . else)
  (w/uniq g-fail
    `(pkc-failcall (pkc-failfn ,g-fail ()
                     (let ,success
                            (pkc-failcall* ,func ,g-fail ,@args)
                       ,then))
                   (pkc-fn (,failure) ,@else))))

(mac pkc-itifsuccess (call then . else)
  `(pkc-ifsuccess it it ,call ,then ,@else))

(mac pkc-itifsuccess* (call then . else)
  `(pkc-ifsuccess* it it ,call ,then ,@else))

(mac pkc-couldcall (func . args)
  `(pkc-itifsuccess (,func ,@args) pkc.t nil))

(mac pkc-couldcall* (func . args)
  `(pkc-itifsuccess* (,func ,@args) pkc.t nil))

(mac pkc-assume (assumption)
  ; TODO: Determine a good failure message.
  `(or ,assumption (pkc-call fail nil)))

(mac pkc-thunk body
  `(pkc-fn () ,@body))

(mac pkc-itfn body
  `(pkc-fn (it) ,@body))

(mac pkc-relyunwrap (type wrapped)
  `(pkc-relycall pkc.unwrap (pkc ,type) ,wrapped))

; TODO: Determine if these should be changed.
(def pk-truthy (x) x)
(def pk-truth (arc-truth) arc-truth)
(def pk-no (x) no.x)


; For efficiency, this assumes the argument is a character.
(def pk-alpha-id-char (char)
  (or alphadig.char (pos char "+-*/<=>") (< 255 int.char)))

; For efficiency, this assumes the argument is a character.
(def pk-infix-id-char (char)
  (~or pk-alpha-id-char.char (<= int.char 32)))


pk-core-type.t-core-text
pk-core-type.t-core-sip-hype
pk-core-type.t-hyped-sym
pk-core-type.t-white
pk-core-type.t-core-sip-brackets


; depends on Penknife: t-core-text

pk-core-rulebook.ltrim
pk-core-rulebook.rtrim

(def ltrim-list (lst test)
  (zap testify test)
  (ut:xloop rev-margin nil rest lst
    (if (and rest do.test.first)
      (do.next (cons car.rest rev-margin) cdr.rest)
      (list rev.rev-margin rest))))

(def rtrim-list (lst test)
  (map rev (ltrim-list rev.list test)))

(pk-core-rule ltrim (text test) ltrim/core-text
  (pkc-arc-to-list:map [pkc-wrap t-core-text _]
    (ltrim-list (pkc-relyunwrap t-core-text text) [pkc-call test _])))

(pk-core-rule rtrim (text test) ltrim/core-text
  (pkc-arc-to-list:map [pkc-wrap t-core-text _]
    (rtrim-list (pkc-relyunwrap t-core-text text) [pkc-call test _])))


; depends on Penknife: t-core-text

pk-core-rulebook.strict-stringify

; TODO: See what to do about things other than characters.
(pk-core-rule strict-stringify (x) strict-stringify/core-text
  (zap [pkc-relyunwrap t-core-text _] x)
  (pkc-assume:all [isa _ 'char] x)
  ; TODO: See if this can use 'string.
  (pk-wrap t-core-string (sym:coerce x 'string)))

(pk-core-rule strict-stringify (x) strict-stringify/core-string
  (pkc-relyunwrap t-core-string x)
  x)


; depends on Penknife: t-core-text

pk-core-rulebook.fn-if-deend

(pk-core-rule fn-if-deend (seq then else) fn-if-deend/core-text
  (zap [pkc-relyunwrap t-core-text _] seq)
  (iflet (last . rev-past) (rev:pkc-relyunwrap t-core-text _)
    (pkc-call then (pkc-wrap t-core-text rev.rev-past) last)
    pkc-call.else))


; depends on Penknife: t-core-sip-hype the-only strict-stringify
; t-hyped-sym

pk-core-rulebook.parse-identifier

(pk-core-rule parse-identifier (text lexid)
                parse-identifier/core-string
  (withs (pk-string (pkc-relycall pkc.strict-stringify text)
          arc-sym (pkc-call pkc.unwrap pkc.t-core-string pk-string)
          arc-string (string:or arc-sym "nil"))
    (pkc-assume:or (all pk-alpha-id-char arc-string)
                   (all pk-infix-id-char arc-string))
    (pkc-wrap t-hyped-sym (pkc-list pk-string lexid))))

(pk-core-rule parse-identifier (text lexid)
                parse-identifier/t-core-sip-hype
  (let (inner-lexid inner-text)
         (pkc-relyunwrap t-core-sip-hype (pkc:the-only text))
    (pkc-relycall pkc.parse-identifier inner-text inner-lexid)))


; depends on Penknife: t-white

; TODO: Figure out a design that doesn't have this horrible horrible
; bottleneck.
pk-core-rulebook.whiteish

(pk-core-rule whiteish (x) whiteish/default
  pk-truth.nil)

(pk-core-rule whiteish (x) whiteish/white
  (pkc-relyunwrap t-white x)
  pk-truth.t)

(pk-core-rule whiteish (x) whiteish/core
  (pkc-assume whitec.x)
  pk-truth.t)


; depends on Penknife: whiteish ltrim rtrim

pk-core-rulebook.empty

(pk-core-rule empty (seq) empty/ifdecap
  (pkc-relycall pkc.fn-ifdecap seq
    (pkc-fn (first rest) pk-truth.t)
    (pkc-thunk pk-truth.nil)))

(pk-core-fun the-only (singleton)
  ; TODO: Come up with better failure messages.
  (pkc-relycall pkc.fn-ifdecap singleton
    (pkc-fn (first rest)
      (pkc-relycall pkc.fn-ifdecap rest
        (pkc-fn (first rest) (pkc-call fail nil))
        pkc-thunk.word))
    (pkc-thunk:pkc-call fail nil)))

(pk-core-fun fn-ifword-custom (text test then else)
  (pkc-call*
    (pkc-fn (margin rest)
      (pkc-call* (pkc-fn (word rest)
                   (if (pk-truthy:pkc:empty word)
                     pkc-call.else
                     (pkc-call then margin word rest)))
        (pkc:rtrim rest (pkc-itfn:pk-no:pkc-call test it))))
    (pkc-relycall pkc.rtrim text test)))

(pk-core-fun fn-iflastword-custom (text test then else)
  (pkc-call*
    (pkc-fn (past margin)
      (pkc-call* (pkc-fn (past word)
                   (if (pk-truthy:pkc:empty word)
                     pkc-call.else
                     (pkc-call then past word margin)))
        (pkc:ltrim past (pkc-itfn:pk-no:pkc-call test it))))
    (pkc-relycall pkc.ltrim text test)))

(pk-core-fun fn-ifword (text then else)
  (pkc-relycall pkc.fn-ifword-custom pkc.whiteish text then else))

(pk-core-fun the-only-word (whiteish text)
  ; TODO: Come up with better failure messages.
  (pkc-relycall pkc.fn-ifword-custom pkc.whiteish text
    (pkc-fn (margin word rest)
      (pkc-relycall pkc.fn-ifword-custom pkc.whiteish rest
        (pkc-fn (margin word rest) (pkc-call fail nil))
        pkc-thunk.word))
    (pkc-thunk:pkc-call fail nil)))

(pk-core-fun the-only-white-word (text)
  (pkc-relycall pkc.the-only-word pkc.whiteish text))


; depends on Penknife: fn-iflastword-custom empty
; parse-infix-expression parse-noninfix-expression

pk-core-rulebook.parse-expression

(pk-core-rule parse-expression (text lexid static-hyperenv)
                parse-expression/parse-noninfix-expression
  (pkc-relycall
    pkc.parse-noninfix-expression text lexid static-hyperenv))

(pk-core-rule parse-expression (text lexid static-hyperenv)
                parse-expression/infix
  (pkc-relycall pkc.fn-iflastword-custom text
    (pkc-itfn:pk-truth:~case type.it char pk-infix-id-char.it)
    (pkc-fn (left op right)
      (pkc-assume:pk-truthy:pkc:empty left)
      (pkc:parse-infix-expression
        left op right lexid static-hyperenv))
    ; TODO: Come up with a better failure message.
    (pkc-thunk:pkc-call fail nil)))


; depends on Penknife: fn-if-deend t-core-sip-brackets
; parse-form-expression hyperenv-get-var-expression parse-identifier
; parse-sip-expression the-only

pk-core-rulebook.parse-noninfix-expression

(pk-core-rule parse-noninfix-expression (text lexid static-hyperenv)
                parse-noninfix-expression/parse-sip-expression
  (pkc-relycall pkc.parse-sip-expression
    (pkc-relycall pkc.the-only text) lexid static-hyperenv))

(pk-core-rule parse-noninfix-expression (text lexid static-hyperenv)
                parse-noninfix-expression/parse-identifier
  (pkc:hyperenv-get-var-expression static-hyperenv
    (pkc-relycall pkc.parse-identifier text lexid)))

(pk-core-rule parse-noninfix-expression (text lexid static-hyperenv)
                parse-noninfix-expression/prefix
  (pkc:fn-if-deend text
    (pkc-fn (past last)
      (let body (pkc-relyunwrap t-core-sip-brackets sip)
        (pkc:parse-form-expression
          past body lexid static-hyperenv)))
    ; TODO: Come up with a better failure message.
    (pkc-thunk:pkc-call fail nil)))


; depends on Penknife: t-core-sip-brackets fn-ifword
; parse-form-expression t-core-sip-hype parse-expression

pk-core-rulebook.parse-sip-expression

(pk-core-rule parse-sip-expression (sip lexid static-hyperenv)
                parse-sip-expression/sip-hype
  (let (inner-lexid text) (pkc-relyunwrap t-core-sip-hype sip)
    (pkc-relycall
      pkc.parse-expression text inner-lexid static-hyperenv)))

(pk-core-rule parse-sip-expression (sip lexid static-hyperenv)
                parse-sip-expression/sip-brackets
  (let text (pkc-relyunwrap t-core-sip-brackets sip)
    (pkc-relycall pkc.fn-ifword text
      (pkc-fn (margin op rest)
        (pkc:parse-form-expression op rest lexid static-hyperenv))
      ; TODO: Come up with a better failure message.
      (pk-thunk:pkc-call fail nil))))


; depends on Penknife: express-form parse-expression

pk-core-rulebook.parse-form-expression

(pk-core-rule parse-form-expression (op body lexid static-hyperenv)
                parse-form-expression/express-form
  (pkc:express-form
    (pkc-relycall pkc.parse-expression op lexid static-hyperenv)
    body lexid static-hyperenv))

pk-core-rulebook.parse-infix-expression

(pk-core-rule parse-infix-expression (left op right lexid
                                      static-hyperenv)
                parse-infix-expression/express-form
  (pkc:express-form (pkc-relycall pkc.parse-form-expression
                      op left lexid static-hyperenv)
                    right lexid static-hyperenv))


; depends on Penknife: express-calculation parse-expression

pk-core-rulebook.parse-calculation

(pk-core-rule parse-calculation (text lexid static-hyperenv)
                parse-calculation/express-calculation
  (pkc:express-calculation:pkc-relycall pkc.parse-expression
    text lexid static-hyperenv))


; Maybe the REPL would be like this:
;
; [rule tl [hyperenv]
;   assume:core-hyperenv-ish.hyperenv
;   [let parsed tl-incremental-parse.hyperenv
;     [let identified [tl-identify hyperenv parsed]
;       [itifexception [tl-eval hyperenv identified]
;         [itifmaybe tl-should-quit.hyperenv
;           it
;          do [tl-report-error hyperenv it]
;             tl:tl-next-hyperenv.hyperenv]
;        do
;         [itifmaybe tl-should-quit.hyperenv
;           it
;          do [tl-report-result hyperenv it]
;             tl:tl-next-hyperenv.hyperenv]]]]]
;
;
; Or maybe it would be more like this:
;
; [rule tl-repl [hyperenv]
;   assume:core-hyperenv-ish.hyperenv
;   [tl-eval-report-loop hyperenv
;     [tl-identify hyperenv tl-incremental-parse.hyperenv]]]
