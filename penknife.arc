; penknife.arc


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


; This implements the Penknife programming language, a Blade-like
; scripting language (which may mean nothing to you, since Blade is a
; vaporware hobby project ^_^ ). Penknife, like Blade, is a language
; that emphasizes the use of whatever syntaxes the programmer finds
; best in every situation.
;
; Unlike Blade, which statically compiles a directory structure,
; delaying compilation of certain declarations until the necessary
; syntaxes are known, Penknife interprets an ongoing character stream,
; invoking imperative commands one at a time to build up its
; definition space. This makes it suitable as a REPL language.
;
; Penknife, like Blade, emphasizes a programming style by which
; convenient sub-languages are developed first, and then they're used
; to build data structures that are compiled into whatever performant
; or rigorous forms are necessary. A Penknife program may indeed have
; some behaviors in common with a build script, making system calls to
; invoke machine code compilers, archival utilities, documentation
; generators, and so forth--but without necessarily having any
; non-Penknife code in the project, instead generating that code as
; part of the build process.
;
;
; To use Penknife, you'll need a working Arc setup (either official
; Arc 3.1[1][2][3], Anarki [2][3][4], Jarc [5], or Rainbow [6]), and
; you'll need to have the Lathe library[7]. Note that Penknife is
; *extremely* slow on Jarc 17, and it's not actually a self-sufficient
; language on any of these platforms, since the global Penknife
; environment only has a few test functions and has neither a way to
; define new functions nor a way to run arbitrary Arc code. Right now,
; you're expected to implement those things yourself! It's an
; adventure~! :-p
;
; [1] http://arclanguage.org/item?id=10254
;       "Arc 3.1 (works on latest MzScheme)"
; [2] http://arclanguage.org/item?id=10625
;       "Arc3.1 setuid problem on Windows"
; [3] http://racket-lang.org/ (Racket)
; [4] http://github.com/nex3/arc (Anarki)
; [5] http://jarc.sourceforge.net/
; [6] http://github.com/conanite/rainbow
; [7] http://github.com/rocketnia/lathe


; Declaration listing:
;
; ut   ; namespace of Lathe's utils.arc
; dy   ; namespace of Lathe's dyn.arc
; mr   ; namespace of Lathe's multival/multirule.arc
; rc   ; namespace of Lathe's orc/orc.arc
; sn   ; namespace of Lathe's imp/sniff.arc
; jv   ; namespace of Lathe's imp/jvm.arc
; plt  ; taken out of Lathe's imp/sniff.arc
; jvm  ; taken out of Lathe's imp/jvm.arc
;
; (fn-input-ify self)  ; rulebook
;
; (newline-normalizer str)
; (comment-ignorer str comment-char)
;
; (start-word str (o test ~whitec))
; (finish-bracket-word str (o test whitec))
; (finish-brackets str)
;
; (soup-whitec x)
; (orev self)                                     ; rulebook
; (o-ltrim self (o test soup-whitec))             ; rulebook
; (o-rtrim self (o test soup-whitec))             ; rulebook
; (oi.olen< self number)                          ; external rule
; (osplit self i)                                 ; rulebook
; (oref self i (o default))                       ; rulebook
; (o-split-first-token seq (o test soup-whitec))
; (o-split-last-token seq (o test soup-whitec))
; (otokens seq (o test soup-whitec))
; (slurp+ a b)                                    ; rulebook
; (o+binary a b)                                  ; rulebook
; (o+ first . rest)
; (soup->string soup)
; (slurp->string self)                            ; rulebook
; (soup->list soup)
; (slurp->list self)                              ; rulebook
; pk-empty-soup*            ; value of type 'pk-soup
; (pk-soup-singleton elem)
;
; (pk-fork-to-get self)                               ; rulebook
; (pk-fork-to-set self new-value)                     ; rulebook
; (pk-fork-to-meta self)                              ; rulebook
; (pk-fork-to-op-method self)                         ; rulebook
; (pk-fork-to-op op-fork body lexid static-hyperenv)
;
; (pk-meta . args)                      ; macro
; (pk-demeta meta)
; (pk-make-ad-hoc-binding value)
; (pk-make-ad-hoc-binding-meta value)
; (pk-binding-get self)                 ; rulebook
; (pk-binding-get-meta self)            ; rulebook
; (pk-binding-set self new-value)       ; rulebook
; (pk-binding-set-meta self new-value)  ; rulebook
;
; (pk-make-interactive-env)
; (pk-staticenv-get-var-forker staticenv hyped-varname globalenv)
; (pk-staticenv-default-op-parser self)        ; rulebook
; pk-comment-char*                             ; value of type 'char
; (pk-staticenv-read-parse-tl self lexid str)  ; rulebook
; (pk-staticenv-literal self name)             ; rulebook
; (pk-dynenv-ensure-binding self varname)      ; rulebook
; (pk-dynenv-get-binding self varname)         ; rulebook
; (pk-dynenv-get self varname)                 ; rulebook
; (pk-dynenv-get-meta self varname)            ; rulebook
; (pk-dynenv-set self varname)                 ; rulebook
; (pk-dynenv-set-meta self varname)            ; rulebook
;
; (pk-hyped-sym-lexid hyped-sym)
; (pk-hyped-sym-name hyped-sym)
; (rc.oiso2 a b)                  ; external rule
;
; (pk-make-hyperenv . args)
; (pk-hyperenv-get hyperenv lexid)
; (pk-hyperenv-get-global hyperenv lexid)
; (pk-hyperenv-get-both hyperenv lexid)
; (pk-hyperenv-combine a b)
; (pk-hyperenv-shove place hyperenv-part error)                ; macro
; (pk-hyperenv-overlap a b)
; (pk-hyperenv-globals hyperenv)
; (pk-dyn-hyperenv-ensure-binding hyperenv hyped-varname)
; (pk-dyn-hyperenv-get hyperenv hyped-varname)
; (pk-dyn-hyperenv-get-meta hyperenv hyped-varname)
; (pk-dyn-hyperenv-set hyperenv hyped-varname new-value)
; (pk-dyn-hyperenv-set-meta hyperenv hyped-varname new-value)
;
; pk-attach-param*                ; value satisfying dy!aparam
; (fn-pk-noattach body)
; (pk-noattach . body)            ; macro
; (fn-pk-attach body (o built-up-hyperenv missing))
; (pk-attach . body)              ; macro
; (pk-attach-to hyperenv . body)  ; macro
; (fn-pk-detach body)
; (pk-detach . body)              ; macro
; (pk-detachmap seq)
;
; (pk-parse-leaf-from-thunk staticenv getter)
; (pk-parse-literal-from-thunk value-parser staticenv)
; (pk-parse-call-from-thunk op-and-body-parser op-parser)
; (pk-var-forker-from-op op-parser)
;
; (pk-function-call-parser op-fork body lexid static-hyperenv)
;
; (pk-alpha-id-char char)
; (pk-infix-id-char char)
; (pk-string-identifier-with-env string lexid env)
; (pk-soup-identifier-with-env soup lexid env)
; (pk-soup-identifier soup lexid)
; (pk-identifier-list soup lexid env)
; (pk-parse-tl soup lexid static-hyperenv)          ; rulebook
; (pk-parse soup lexid static-hyperenv)             ; rulebook
; (pk-parse-sip self lexid static-hyperenv)         ; rulebook
;
; pk-defuse-param*            ; value satisfying dy!aparam
; (pk-defuse body afterward)
; (pk-err contents)
;
; (pk-call self . args)       ; rulebook
; (pk-call-set self . args)   ; rulebook
; (pk-call-meta self . args)  ; rulebook
;
; (def-pk-eval type . body)               ; macro
; (def-pk-eval-meta type . body)          ; macro
; (pk-eval self lexid dyn-hyperenv)       ; rulebook
; (pk-eval-meta self lexid dyn-hyperenv)  ; rulebook
;
; pk-repllexid*  ; symbol to be used as a lexid (lexical ID)
; pk-replenv*    ; value of type 'pk-interactive-env
;
; (error-message error)
; (pktl act-on report-error nextmeta)
; (pktl-stream lexid env str act-on report-error prompt)
; (pkrepl (o str missing))
; (pkdo lexid env str)
; (pkload lexid env filename)
; (pkparse str)
;
;
; Type listing:
;
; fn-input
;   rep: A function simulating a character input stream, which
;        supports the following operations:
;   rep._!ready:  Returns t if the stream is guaranteed not to block
;                 during the next peek or read attempt, or nil if no
;                 such guarantee can be made.
;   rep._!peek:   Blocks if necessary and returns the next character
;                 in the stream without consuming it. On end-of-file,
;                 this returns nil.
;   rep._!read:   Blocks if necessary and returns the next character
;                 in the stream, consuming it. On end-of-file, this
;                 returns nil.
;
; pk-soup
;   rep: A proper list containing nonempty sequences (called "slurps")
;        which contain arbitrary elements (called "sips"). This is
;        merely a list format which is specialized for holding
;        elements that make sense to keep in dedicated string types,
;        such as characters and bytes.
;
; pk-sip-whitec
;   rep: Ignored. This value indicates a whitespace sip that doesn't
;        correspond to any particular character.
;
; pk-sip-brackets
;   rep: A singleton proper list containing a value of type 'pk-soup.
;        This is soup which is semantically understood as being the
;        interior of a pair of brackets. It often appears as a sip in
;        another pk-sip-brackets's soup in order to represent nested
;        brackets.
;
; pk-lambdacalc-literal
;   rep: A singleton list containing the value for this expression to
;        evaluate to.
;
; TODO: See if this is still useful.
; pk-lambdacalc-literal-meta
;   rep: A singleton list containing the metadata for this expression
;        to evaluate to.
;
; pk-lambdacalc-var
;   rep: A 'pk-hyped-sym value representing the variable to look up in
;        the dynamic hyperenvironment when evaluating this expression.
;
; pk-lambdacalc-var-meta
;   rep: A 'pk-hyped-sym value representing the variable to look up in
;        the dynamic hyperenvironment when evaluating this expression.
;        This looks up the 'pk-ad-hoc-meta metadata table
;        corresponding to the variable.
;
; pk-lambdacalc-set
;   rep: A list which supports the following fields:
;   rep._.0:  A 'pk-hyped-sym value representing the variable to
;             modify in the dynamic hyperenvironment when evaluating
;             this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will provide the new value for the variable
;             (which will also be the result of this expression). If
;             the new value has special metadata, that metadata will
;             be ignored, and it won't even be returned by this
;             expression.
;
; pk-lambdacalc-set-meta
;   rep: A list which supports the following fields:
;   rep._.0:  A 'pk-hyped-sym value representing the variable to
;             modify in the dynamic hyperenvironment when evaluating
;             this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, whose non-metadata result will provide the new
;             metadata for the variable (and which will also be the
;             non-metadata result of this expression).
;
; pk-lambdacalc-call
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call.
;
; pk-lambdacalc-call-set
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call-set.
;
; pk-lambdacalc-call-meta
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call-meta.
;
; pk-lambdacalc-demeta
;   rep: A singleton proper list containing a
;        'pk-lambdacalc-[something] expression, which should be
;        evaluated for its metadata so that that metadata can be
;        returned as the non-metadata result of this expression.
;
; pk-parse-fork
;   rep: A table which supports the following fields:
;   rep._!get:   A value which, when called using 'pk-call, accepts no
;                arguments and returns a 'pk-attached-lambdacalc
;                value, representing an expression that returns a
;                value to be used in a parent expression.
;   rep._!set:   A value which, when called using 'pk-call, accepts
;                one 'pk-attached-lambdacalc value and returns another
;                that sets something to the value returned by the
;                first expression.
;   rep._!meta:  A value which, when called using 'pk-call, accepts no
;                arguments and returns a 'pk-attached-lambdacalc
;                value, representing an expression that returns a
;                value to be used by a top-level command interpreter.
;   rep._!op:    A value which, when called using 'pk-call or
;                'pk-call-meta, accepts this very 'pk-parse-fork value
;                (the parsed operator), a 'pk-soup value (the unparsed
;                body), an lexid (lexical ID), and a static
;                hyperenvironment (a 'pk-hyperenv value) and returns a
;                'pk-parse-fork value representing the parsed
;                expression.
;
; pk-ad-hoc-binding
;   rep: A list which supports getting and setting the following
;        field:
;   rep._.0:  A value of type 'pk-ad-hoc-meta, representing the
;             metadata associated with the variable represented by
;             this binding.
;
; pk-interactive-env
;   rep: A nullary function returning a table mapping bound variable
;        names to singleton proper lists containing their bindings.
;        The table returned is the same one each time, so that
;        'pk-dynenv-ensure-binding can mutate new bindings onto it.
;        The point of having this be a function, rather than just
;        being the table itself, is so that Jarc 17 and Rainbow don't
;        error out when trying to display an environment which has an
;        element that refers back to the same environment.
;
; pk-hyperenv
;   rep: A table mapping lexids ("lexical IDs," which identify
;        independent sections of textual code) to two-element proper
;        lists supporting the following fields:
;   rep._.lexid.0:  A local environment.
;   rep._.lexid.1:  A global environment corresponding to that local
;                   environment.
;
; pk-hyped-sym
;   rep: A list which supports the following fields, which together
;        indicate a specific variable in a specific environment in a
;        hyperenvironment:
;   rep._.0:  A symbol to be used as a lexid (lexical ID).
;   rep._.1:  A symbol to be used as a variable name.
;
; pk-sip-hype-staticenv
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol to be used as a lexid (lexical ID).
;   rep._.1:  An environment to use as the global environment
;             associated with that lexid in the global dynamic
;             hyperenvironment when evaluating the expression
;             resulting from this syntax.
;   rep._.2:  A 'pk-soup word to be compiled using that lexid.
;
; pk-attached-lambdacalc
;   rep: A list which supports the following fields:
;   rep._.0:  A hyperenvironment containing global environments to use
;             when evaluating this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types.
;
; pk-fn-meta
;   rep: A singleton proper list containing a Penknife function which
;        returns a value of type 'pk-ad-hoc-meta. The inner function
;        will be called using 'pk-call using the arguments from this
;        object's 'pk-call or 'pk-call-meta, but only 'pk-call-meta
;        will return the full command metadata.
;
; pk-ad-hoc-meta
;   rep: A table which supports the following fields:
;   rep._!result:      The value to use as the result in any context
;                      other than the top-level one. This is the only
;                      non-optional field; if this is nil, then the
;                      value used is actually nil itself.
;   rep._!action:      If present, a singleton proper list containing
;                      a Penknife value which, when called with no
;                      arguments using 'pk-call, will imperatively
;                      perform some additional action which is meant
;                      to be done instead of writing the result to the
;                      REPL.
;   rep._!quit:        If present, a singleton proper list indicating
;                      that the Penknife REPL session should exit and
;                      return the contained value to the Arc REPL.
;   rep._!var-forker:  If present, a singleton proper list containing
;                      a Penknife function which, when given a
;                      'pk-hyped-sym variable name and a global static
;                      environment, will return a 'pk-parse-fork
;                      value. If instead this is nil, then a default
;                      parse fork should be constructed according to
;                      that environment's own behavior.
;   rep._!error:       If present, a singleton proper list containing
;                      the value to raise as an error message whenever
;                      the result, but not this metadata, is looked up
;                      in a binding or environment.


(let lathe [+ lathe-dir* _ '.arc]
  (use-fromwds-as ut do.lathe!utils
                  dy do.lathe!dyn
                  mr do.lathe!multival/multirule
                  rc do.lathe!orc/orc
                  oi do.lathe!orc/oiter
                  sn do.lathe!imp/sniff
                  jv do.lathe!imp/jvm))

(= plt sn.plt jvm jv.jvm)


(rc:ontype fn-input-ify () fn-input fn-input
  self)

(rc:ontype fn-input-ify () string string
  (fn-input-ify instring.self))

; NOTE: Rainbow doesn't even define 'peekc. That actually doesn't
; affect us yet, since we're going through low-level hoops to get
; ready-testing behavior already, but it might be good to know.
(rc:ontype fn-input-ify () input input
  (when jvm
    ; The 'errsafe here is because Jarc translates 'input values to
    ; Readers, whereas Rainbow translates them to InputStreams. After
    ; this expression, we can be sure 'self is something that can be
    ; used as a Reader--either the reader we create, or the original
    ; value of 'self.
    (errsafe:zap jvm!java-io-InputStreamReader-new self)
    ; TODO: See if BufferedReader would be better.
    (zap jvm!java-io-PushbackReader-new self))
  (annotate 'fn-input
    ; This is critical enough that we're special-casing each Java
    ; implementation rather than using the interpreted 'jvm DSL
    ; multiple times per character read.
    (if sn.jarcdrop*
      (with (jready   (jarc.JavaInstanceMethod.find self "ready" nil)
             jread    (jarc.JavaInstanceMethod.find self "read" nil)
             ; This #\a is just a sample character.
             junread  (jarc.JavaInstanceMethod.find
                        self "unread" '(#\a)))
        (fn ((o mode 'read))
          (case mode
            ready  do.jready.self
            peek   (caselet charcode do.jread.self -1 nil
                     (do (do.junread self charcode)
                         (coerce charcode 'char)))
            read   (caselet charcode do.jread.self -1 nil
                     (coerce charcode 'char))
                   (err "Illegal fn-input option."))))
        sn.rainbowdrop*
      (fn ((o mode 'read))
        (case mode
          ready  (java-invoke self 'ready nil)
          peek   (caselet charcode (java-invoke self 'read nil) -1 nil
                   (do (java-invoke self 'unread list.charcode)
                       (coerce charcode 'char)))
          read   (caselet charcode (java-invoke self 'read nil) -1 nil
                   (coerce charcode 'char))
                 (err "Illegal fn-input option.")))
      (fn ((o mode 'read))
        (case mode
          ready  (~~and plt plt.char-ready?.self)
          peek   peekc.self
          read   readc.self
                 (err "Illegal fn-input option."))))))


; This translates "\r\n" and "\r" sequences to "\n".
(def newline-normalizer (str)
  (zap fn-input-ify str)
  (withs (just-returned nil
          read (thunk:ut:ret char rep.str!read
                 (= just-returned (is char #\return)))
          peek (fn (blocking)
                 ; This returns a singleton list containing the next
                 ; character in the stream, ignoring any #\newline
                 ; that comes after a #\return, translating any
                 ; #\return to a #\newline, and not consuming the
                 ; resulting character. On end-of-file, this returns a
                 ; singleton list containing nil. If blocking is nil
                 ; and the wrapped stream isn't known to have a
                 ; character ready, this returns nil.
                 (catch:while (or blocking rep.str!ready)
                   (let char rep.str!peek
                     (if (case char #\newline just-returned)
                       call.read
                       (throw:list:case char #\return #\newline
                         char))))))
    (annotate 'fn-input
      (fn ((o mode 'read))
        (case mode
          ; NOTE: Jarc doesn't like ~ by itself, so we're using '~no
          ; instead of '~~ here.
          ready  (~no do.peek.nil)
          peek   do.peek.t.0
          read   (do1 do.peek.t.0 call.read)
                 (err "Illegal fn-input option."))))))

(def comment-ignorer (str comment-char)
  (zap fn-input-ify str)
  (withs (in-comment nil
          peek (fn (blocking)
                 ; This returns a singleton list containing the next
                 ; character in the stream, ignoring comments, and
                 ; without consuming that character. On end-of-file,
                 ; this returns a singleton list containing nil. If
                 ; blocking is nil and the wrapped stream isn't known
                 ; to have a character ready, this returns nil.
                 (catch:while (or blocking rep.str!ready)
                   (let char rep.str!peek
                     (when (if in-comment
                             (or no.char (pos char "\r\n"))
                             (is char comment-char))
                       (zap no in-comment))
                     (if in-comment
                       rep.str!read
                       (throw list.char))))))
    (annotate 'fn-input
      (fn ((o mode 'read))
        (case mode
          ; NOTE: Jarc doesn't like ~ by itself, so we're using '~no
          ; instead of '~~ here.
          ready  (~no do.peek.nil)
          peek   do.peek.t.0
          read   (do1 do.peek.t.0 rep.str!read)
                 (err "Illegal fn-input option."))))))


; NOTE: Rainbow's profiler doesn't like function calls in optional
; arguments, but it can actually handle this one.
(def start-word (str (o test ~whitec))
  (zap rc.otestify test)
  (zap fn-input-ify str)
  (w/outstring s
    (catch:whilet char (or rep.str!peek rep.str!read)  ; Consume EOF.
      (if do.test.char
        (throw inside.s)
        (disp rep.str!read s)))))

(def finish-bracket-word (str (o test whitec))
  (zap rc.otestify test)
  (zap fn-input-ify str)
  (annotate 'pk-soup
    (accum acc
      (with (chars (outstring) nonchars nil)
        (while:caselet char (or rep.str!peek rep.str!read) #\[
          (do rep.str!read
              (only.acc:check inside.chars ~empty)
              (= chars (outstring))
              (push (annotate 'pk-sip-brackets
                      (list finish-brackets.str))
                    nonchars))
          (if (or no.char do.test.char)
            (do (only.acc:check inside.chars ~empty)
                (.nonchars:only acc:rev)
                nil)
            (do (.nonchars:only acc:rev)
                wipe.nonchars
                (writec rep.str!read chars)
                ; NOTE: On Rainbow, 'writec returns nil rather than
                ; the character written.
                t)))))))

(def finish-brackets (str)
  (zap fn-input-ify str)
  (do1 (finish-bracket-word str #\])
       rep.str!read))


(def soup-whitec (x)
  (case type.x char whitec.x rc.a-!pk-sip-whitec.x))

(rc:ontype orev () string string
  (tostring:down i (- len.self 1) 0
    (writec self.i)))

(rc:ontype o-ltrim ((o test soup-whitec)) rc.list list
  (aif (pos (complement rc.otestify.test) self)
    (split self it)
    (list self nil)))

(rc:ontype o-ltrim ((o test whitec)) string string
  (aif (pos (complement rc.otestify.test) self)
    (split self it)
    (list self "")))

(rc:ontype o-ltrim ((o test soup-whitec)) pk-soup pk-soup
  (zap rep self)
  (let margin (accum acc
                (catch:while self
                  (let (before rest) (o-ltrim pop.self test)
                    (unless oi.oempty.rest
                      (push rest self)
                      (unless oi.oempty.before
                        do.acc.before)
                      throw.nil)
                    do.acc.before)))
    (map [annotate 'pk-soup _] (list margin self))))

(rc:ontype o-rtrim ((o test soup-whitec)) rc.list list
  (map rev (rev:o-ltrim rev.self test)))

(rc:ontype o-rtrim ((o test whitec)) string string
  (map orev (rev:o-ltrim orev.self test)))

(rc:ontype o-rtrim ((o test soup-whitec)) pk-soup pk-soup
  (zap rev:rep self)
  (let margin (accum acc
                (catch:while self
                  (let (rest after) (o-rtrim pop.self test)
                    (unless oi.oempty.rest
                      (push rest self)
                      (unless oi.oempty.after
                        do.acc.after)
                      throw.nil)
                    do.acc.after)))
    (map [annotate 'pk-soup rev._] (list self margin))))

; This is used internally by oi!oempty and oi!olen>, and we also use
; it directly.
(rc:ontype oi.olen< (number) pk-soup pk-soup
  (and (< 0 number)
       (catch:~each slurp rep.self
         (unless (oi.olen< slurp number)
           throw.nil)
         (-- number oi.olen.slurp))))

(rc:ontype osplit (i) rc.list list
  (when (<= 0 i)
    (ut:xloop rev-before nil after self i i
      (case i 0
        (list rev.rev-before after)
        (whenlet (first . rest) after
          (do.next (cons first rev-before) rest (- i 1)))))))

(rc:ontype osplit (i) string string
  (errsafe:split self i))

; TODO: See if this can be more elegant.
(rc:ontype osplit (i) pk-soup pk-soup
  (zap rep self)
  (point return
    (unless (<= 0 i)
      do.return.nil)
    (let before (accum acc
                  (while:case i 0 nil
                    (case self nil
                      do.return.nil
                      (let slurp pop.self
                        (iflet (slurp-before slurp-after)
                                 (osplit slurp i)
                          (do (unless oi.oempty.slurp-before
                                do.acc.slurp-before)
                              (unless oi.oempty.slurp-after
                                (push slurp-after self))
                              nil)
                          (do do.acc.slurp
                              (-- i oi.olen.slurp)))))))
      (map [annotate 'pk-soup _] (list before self)))))

(rc:ontype oref (i (o default)) rc.list list
  (on-err [do default] (fn () self.i)))

(rc:ontype oref (i (o default)) string string
  (on-err [do default] (fn () self.i)))

(w/uniq missing
  (rc:ontype oref (i (o default)) pk-soup pk-soup
    (when (<= 0 i)
      (catch:each slurp rep.self
        (let elem (oref slurp i missing)
          (unless (is elem missing)
            throw.elem)
          (unless (<= 0 (-- i oi.olen.slurp))
            throw.default))))))

(def o-split-first-token (seq (o test soup-whitec))
  (zap rc.otestify test)
  (let (margin rest) (o-ltrim seq test)
    (awhen (check (o-ltrim rest ~test) ~oi.oempty:car)
      (cons margin it))))

(def o-split-last-token (seq (o test soup-whitec))
  (zap rc.otestify test)
  (let (rest margin) (o-rtrim seq test)
    (awhen (check (o-rtrim rest ~test) ~oi.oempty:cadr)
      (join it list.margin))))

(def otokens (seq (o test soup-whitec))
  (zap rc.otestify test)
  (accum acc
    (ut:dstwhilet (margin token rest) (o-split-first-token seq test)
      do.acc.token
      (= seq rest))))

(rc:ontypes slurp+ (a b) (rc.list rc.list) list-and-list
  (list:+ a b))

(rc:ontypes slurp+ (a b) (rc.list string) list-and-string
  (list a b))

(rc:ontypes slurp+ (a b) (string rc.list) string-and-list
  (list a b))

(rc:ontypes slurp+ (a b) (string string) string-and-string
  (list:+ a b))

(rc:ontypes o+binary (a b) (pk-soup pk-soup) pk-soup-and-pk-soup
  (if oi.oempty.a  b
      oi.oempty.b  a
    (withs (rep-a rep.a
            ; NOTE: Jarc is fine with (let (x (y)) z ...), but it
            ; doesn't allow (let ((x) y) z ...).
            (before (a-slurp))  (split rep-a (- len.rep-a 1))
            (b-slurp after)     (split rep.b 1))
      (zap car b-slurp)
      (annotate 'pk-soup
        (join before (slurp+ a-slurp b-slurp) after)))))

(def o+ (first . rest)
  (ut.foldl o+binary first rest))

(def soup->string (soup)
  ; NOTE: On Rainbow, (apply string '("something")) and
  ; (string '("something")) don't have the same result.
  (catch:apply string (map [or slurp->string._ throw.nil] rep.soup)))

(rc:ontype slurp->string () string string
  self)

(rc:ontype slurp->string () rc.any rc.any
  nil)

(def soup->list (soup)
  (catch:mappend [car:or slurp->list._ throw.nil] rep.soup))

(rc:ontype slurp->list () rc.list list
  list.self)

(rc:ontype slurp->list () rc.any rc.any
  nil)

(= pk-empty-soup* (annotate 'pk-soup nil))

; TODO: See how to make this aware of nonstandard kinds of slurps.
(def pk-soup-singleton (elem)
  (annotate 'pk-soup (list:.elem:case type.elem char string list)))


(rc:ontype pk-fork-to-get () pk-parse-fork pk-parse-fork
  (pk-call rep.self!get))

(rc:ontype pk-fork-to-set (new-value) pk-parse-fork pk-parse-fork
  (pk-call rep.self!set new-value))

(rc:ontype pk-fork-to-meta () pk-parse-fork pk-parse-fork
  (pk-call rep.self!meta))

(rc:ontype pk-fork-to-op-method () pk-parse-fork pk-parse-fork
  rep.self!op)

(def pk-fork-to-op (op-fork body lexid static-hyperenv)
  (pk-call pk-fork-to-op-method.op-fork
    op-fork body lexid static-hyperenv))


(mac pk-meta args
  `(annotate 'pk-ad-hoc-meta (obj ,@args)))

(def pk-demeta (meta)
  (awhen rep.meta!error
    (pk-err car.it))
  rep.meta!result)

; TODO: See if this is ever going to be used.
(def pk-make-ad-hoc-binding (value)
  (pk-make-ad-hoc-binding-meta:pk-meta result value))

(def pk-make-ad-hoc-binding-meta (value)
  (annotate 'pk-ad-hoc-binding list.value))

(rc:ontype pk-binding-get () pk-ad-hoc-binding pk-ad-hoc-binding
  (pk-demeta pk-binding-get-meta.self))

(rc:ontype pk-binding-get-meta () pk-ad-hoc-binding pk-ad-hoc-binding
  rep.self.0)

(rc:ontype pk-binding-set (new-value)
             pk-ad-hoc-binding pk-ad-hoc-binding
  (pk-binding-set-meta self (pk-meta result new-value))
  new-value)

(rc:ontype pk-binding-set-meta (new-value)
             pk-ad-hoc-binding pk-ad-hoc-binding
  (= rep.self.0 new-value))


(def pk-make-interactive-env ()
  (let rep (table) (annotate 'pk-interactive-env thunk.rep)))

(def pk-staticenv-get-var-forker (staticenv hyped-varname globalenv)
  (aif (aand (pk-dynenv-get-binding
               staticenv pk-hyped-sym-name.hyped-varname)
             (!var-forker:rep:pk-binding-get-meta car.it))
    (pk-call car.it hyped-varname globalenv)
    (let op-parser pk-staticenv-default-op-parser.staticenv
      (pk-call pk-var-forker-from-op.op-parser
        hyped-varname globalenv))))

(rc:ontype pk-staticenv-default-op-parser ()
             pk-interactive-env pk-interactive-env
  pk-function-call-parser)

(= pk-comment-char* #\;)

; TODO: Allow read behavior customization among environments.
(rc:ontype pk-staticenv-read-parse-tl (lexid str)
             pk-interactive-env pk-interactive-env
  (awhen (start-word&finish-bracket-word:comment-ignorer
           str pk-comment-char*)
    (list:pk-parse-tl it lexid (pk-make-hyperenv lexid self))))

; TODO: Allow literal syntax customization among environments.
(rc:ontype pk-staticenv-literal (name)
             pk-interactive-env pk-interactive-env
  (zap [string:or _ "nil"] name)
  (when (all digit name)
    (list int.name)))

; TODO: Figure out how best to make this thread-safe.
; TODO: See if the name ought to be baked into the metadata this way.
(rc:ontype pk-dynenv-ensure-binding (varname)
             pk-interactive-env pk-interactive-env
  (car:or= (.varname:rep.self)
    (list:pk-make-ad-hoc-binding-meta:pk-meta error
      (list:+ "The variable \"" (or varname "nil") "\" "
              "is unbound."))))

(rc:ontype pk-dynenv-get-binding (varname)
             pk-interactive-env pk-interactive-env
  (.varname:rep.self))

(rc:ontype pk-dynenv-get (varname)
             pk-interactive-env pk-interactive-env
  (pk-binding-get:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-get-meta (varname)
             pk-interactive-env pk-interactive-env
  (pk-binding-get-meta:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-set (varname new-value)
             pk-interactive-env pk-interactive-env
  (pk-binding-set (pk-dynenv-ensure-binding self varname) new-value))

(rc:ontype pk-dynenv-set-meta (varname new-value)
             pk-interactive-env pk-interactive-env
  (pk-binding-set-meta
    (pk-dynenv-ensure-binding self varname) new-value))


(def pk-hyped-sym-lexid (hyped-sym)
  rep.hyped-sym.0)

(def pk-hyped-sym-name (hyped-sym)
  rep.hyped-sym.1)

; This is used internally by rc.opos.
(rc:ontypes rc.oiso2 (a b) (pk-hyped-sym pk-hyped-sym) pk-hyped-sym
  (iso rep.a rep.b))


(def pk-make-hyperenv args
  (annotate 'pk-hyperenv
    (apply copy (table)
      (mappend [list _.0 (list _.1 _.1)] pair.args))))

(def pk-hyperenv-get (hyperenv lexid)
  (car:pk-hyperenv-get-both hyperenv lexid))

(def pk-hyperenv-get-global (hyperenv lexid)
  (cadr:pk-hyperenv-get-both hyperenv lexid))

(def pk-hyperenv-get-both (hyperenv lexid)
  (or rep.hyperenv.lexid
      (err:+ "A hyperenvironment was indexed with an unsupported "
             "lexid: " (tostring write.hyperenv) " with "
             (tostring write.lexid))))

(def pk-hyperenv-combine (a b)
  (zap rep a)
  (catch:annotate 'pk-hyperenv
    (ut:ret result copy.a
      (each (lexid (b-local-env b-global-env)) rep.b
        (iflet (a-local-env a-global-env) do.a.lexid
          (unless (and (is a-local-env b-local-env)
                       (is a-global-env b-global-env))
            throw.nil)
          (= do.result.lexid (list b-local-env b-global-env)))))))

(mac pk-hyperenv-shove (place hyperenv-part error)
  (w/uniq g-prev
    `(zap (fn (,g-prev)
            (or (pk-hyperenv-combine ,g-prev ,hyperenv-part)
                (err ,error)))
          ,place)))

(def pk-hyperenv-overlap (a b)
  (annotate 'pk-hyperenv (ut.tab+ rep.a rep.b)))

(def pk-hyperenv-globals (hyperenv)
  (annotate 'pk-hyperenv
    (listtab:accum acc
      (each (lexid (local-env global-env)) rep.hyperenv
        (do.acc:list lexid (list global-env global-env))))))

(def pk-dyn-hyperenv-ensure-binding (hyperenv hyped-varname)
  (let (lexid varname) rep.hyped-varname
    (pk-dynenv-ensure-binding
      (pk-hyperenv-get hyperenv lexid) varname)))

(def pk-dyn-hyperenv-get (hyperenv hyped-varname)
  (let (lexid varname) rep.hyped-varname
    (pk-dynenv-get (pk-hyperenv-get hyperenv lexid) varname)))

(def pk-dyn-hyperenv-get-meta (hyperenv hyped-varname)
  (let (lexid varname) rep.hyped-varname
    (pk-dynenv-get-meta (pk-hyperenv-get hyperenv lexid) varname)))

(def pk-dyn-hyperenv-set (hyperenv hyped-varname new-value)
  (let (lexid varname) rep.hyped-varname
    (pk-dynenv-set
      (pk-hyperenv-get hyperenv lexid) varname new-value)))

(def pk-dyn-hyperenv-set-meta (hyperenv hyped-varname new-value)
  (let (lexid varname) rep.hyped-varname
    (pk-dynenv-set-meta
      (pk-hyperenv-get hyperenv lexid) varname new-value)))


(= pk-attach-param* dy.make-param.nil)

(def fn-pk-noattach (body)
  (dy:param-let pk-attach-param* nil
    call.body))

(mac pk-noattach body
  `(fn-pk-noattach:fn () ,@body))

; NOTE: Rainbow's profiler doesn't like function calls in optional
; arguments.
(w/uniq missing
  (def fn-pk-attach (body (o built-up-hyperenv missing))
    (when (is built-up-hyperenv missing)
      (= built-up-hyperenv (pk-make-hyperenv)))
    (dy:param-let pk-attach-param*
                    [pk-hyperenv-shove built-up-hyperenv _
                      (+ "A 'pk-detach block resulted in a "
                         "hyperenvironment part that conflicted with "
                         "others in the same 'pk-attach block.")]
      (let unattached-lambdacalc call.body
        (annotate 'pk-attached-lambdacalc
          (list built-up-hyperenv unattached-lambdacalc))))))

(mac pk-attach body
  `(fn-pk-attach:fn () ,@body))

(mac pk-attach-to (hyperenv . body)
  `(fn-pk-attach (fn () ,@body) ,hyperenv))

(def fn-pk-detach (body)
  (unless dy.param-get.pk-attach-param*
    (err:+ "A 'pk-detach block was entered outside the context of a "
           "matching 'pk-attach."))
  (let attached-lambdacalc (pk-noattach call.body)
    (case type.attached-lambdacalc pk-attached-lambdacalc nil
      (err:+ "The inside of a 'pk-detach block didn't result in a "
             "'pk-attached-lambdacalc value."))
    (let (hyperenv-part expr) rep.attached-lambdacalc
      (.hyperenv-part:or dy.param-get.pk-attach-param*
        (err:+ "A 'pk-detach block was exited outside the context of "
               "a matching 'pk-attach."))
      expr)))

(mac pk-detach body
  `(fn-pk-detach:fn () ,@body))

(mac pk-detachmap (seq)
  `(map [pk-detach _] (pk-noattach ,seq)))


(def pk-parse-leaf-from-thunk (staticenv getter)
  (zap memo getter)
  (annotate 'pk-parse-fork
    (obj get   getter
         set   [err:+ "An attempt was made to parse an ineligible "
                      "form for setting."]
         meta  getter
         op    pk-staticenv-default-op-parser.staticenv)))

(def pk-parse-literal-from-thunk (value-parser staticenv)
  (pk-parse-leaf-from-thunk staticenv
    (thunk:pk-attach:annotate 'pk-lambdacalc-literal
      (list:pk-noattach call.value-parser))))

; The 'op-and-body-parser parameter should be a function that returns
; a proper list of 'pk-attached-lambdacalc values representing the
; function and arguments.
(def pk-parse-call-from-thunk (op-and-body-parser op-parser)
  (zap memo op-and-body-parser)
  (annotate 'pk-parse-fork
    (obj get   (memo:thunk:pk-attach:annotate 'pk-lambdacalc-call
                 (pk-detachmap call.op-and-body-parser))
         set   (let set-parser
                      (memo:thunk:pk-attach:annotate
                        'pk-lambdacalc-call-set
                        (pk-detachmap call.op-and-body-parser))
                 [pk-attach:annotate 'pk-lambdacalc-call
                   (pk-detachmap:list call.set-parser _)])
         meta  (memo:thunk:pk-attach:annotate 'pk-lambdacalc-call-meta
                 (pk-detachmap call.op-and-body-parser))
         op    op-parser)))

(def pk-var-forker-from-op (op-parser)
  (fn (hyped-varname globalenv)
    (let hyperenv (pk-make-hyperenv
                    pk-hyped-sym-lexid.hyped-varname globalenv)
      (annotate 'pk-parse-fork
        (obj get   (memo:thunk:pk-attach-to hyperenv
                     (annotate 'pk-lambdacalc-var hyped-varname))
             set   [pk-attach-to hyperenv
                     (annotate 'pk-lambdacalc-set
                       (list hyped-varname pk-detach._))]
             meta  (memo:thunk:pk-attach-to hyperenv
                     (annotate 'pk-lambdacalc-var-meta hyped-varname))
             op    op-parser)))))


(def pk-function-call-parser (op-fork body lexid static-hyperenv)
  (pk-parse-call-from-thunk
    (thunk:cons pk-fork-to-get.op-fork
      (map [pk-fork-to-get:pk-parse _ lexid static-hyperenv]
           otokens.body))
    (pk-staticenv-default-op-parser:pk-hyperenv-get
      static-hyperenv lexid)))


; For efficiency, this assumes the argument is a character.
(def pk-alpha-id-char (char)
  (or alphadig.char (pos char "+-*/<=>") (< 255 int.char)))

; For efficiency, this assumes the argument is a character.
(def pk-infix-id-char (char)
  (~or pk-alpha-id-char.char (<= int.char 32)))

; This assumes the first argument is a string.
(def pk-string-identifier-with-env (string lexid env)
  (when (or (all pk-alpha-id-char string)
            (all pk-infix-id-char string))
    (list (annotate 'pk-hyped-sym (list lexid sym.string)) env)))

; This assumes the first argument is a 'pk-soup value.
(def pk-soup-identifier-with-env (soup lexid env)
  (aif soup->string.soup
    (pk-string-identifier-with-env it lexid env)
      (~or (oi.olen> soup 1) oi.oempty.soup)
    (let sip (oref soup 0)
      (case type.sip pk-sip-hype-staticenv
        (let (inner-lexid globalenv inner-soup) rep.sip
          (pk-soup-identifier-with-env
            inner-soup inner-lexid globalenv))))))

; This assumes the first argument is a 'pk-soup value.
(def pk-soup-identifier (soup lexid)
  (car:pk-soup-identifier-with-env soup lexid nil))

(def pk-identifier-list (soup lexid)
  (zap otokens soup)
  (unless single.soup
    (err "An identifier list wasn't exactly one word."))
  (zap car soup)
  (unless (and (no oi.oempty.soup) (oi.olen< soup 2))
    (err "An identifier list wasn't exactly one sip: " soup))
  (zap [oref _ 0] soup)
  (case type.soup pk-sip-hype-staticenv
    (let (inner-lexid globalenv inner-soup) rep.soup
      (pk-identifier-list inner-soup inner-lexid))
    (do (case type.soup pk-sip-brackets nil
          (err "An identifier list wasn't a 'pk-sip-brackets."))
        (map [pk-soup-identifier _ lexid] (otokens rep.soup.0)))))

(mr:rule pk-parse-tl (soup lexid static-hyperenv) expression
  (pk-fork-to-meta:pk-parse soup lexid static-hyperenv))

(mr:rule pk-parse (soup lexid static-hyperenv) one-sip
  (when (or (oi.olen> soup 1) oi.oempty.soup soup->string.soup)
    (do.fail "The word wasn't simply a single non-character."))
  (pk-parse-sip (oref soup 0) lexid static-hyperenv))

; TODO: See if this can be simpler.
(mr:rule pk-parse (soup lexid static-hyperenv) identifier
  (iflet (hyped-sym env) (pk-soup-identifier-with-env soup lexid
                           (pk-hyperenv-get static-hyperenv lexid))
    (let (local-env global-env) (pk-hyperenv-get-both
                                  (if env
                                    (pk-hyperenv-overlap
                                      (pk-make-hyperenv lexid env)
                                      static-hyperenv)
                                    static-hyperenv)
                                  lexid)
      (let name pk-hyped-sym-name.hyped-sym
        (iflet (literal) (pk-staticenv-literal local-env name)
          (pk-parse-literal-from-thunk thunk.literal local-env)
          (pk-staticenv-get-var-forker
            local-env hyped-sym global-env))))
    (do.fail "The word wasn't an identifier.")))

(mr:rule pk-parse (soup lexid static-hyperenv) infix
  (iflet (left op right) (o-split-last-token soup
                           [~case type._ char pk-infix-id-char._])
    (if oi.oempty.left
      (do.fail:+ "The word started with its only infix operator, so "
                 "it wasn't an infix form.")
      (ut:lets it (pk-parse op lexid static-hyperenv)
               it (pk-fork-to-op it left lexid static-hyperenv)
                  (pk-fork-to-op it right lexid static-hyperenv)))
    (do.fail "The word didn't contain an infix operator.")))

(mr:rule pk-parse (soup lexid static-hyperenv) prefix
  (let (op bodies) (o-rtrim soup rc.a-!pk-sip-brackets)
    (unless (or (and oi.oempty.op (oi.olen> bodies 1))
                (and (pk-soup-identifier op lexid)
                     (oi.olen> bodies 0)))
      (do.fail:+ "The word wasn't a series of bracketed bodies "
                 "preceded by a bracket form or an identifier."))
    (zap soup->list bodies)
    (= op (if oi.oempty.op
            (pk-parse-sip pop.bodies lexid static-hyperenv)
            (pk-parse op lexid static-hyperenv)))
    (each body (map car:rep bodies)
      (zap [pk-fork-to-op _ body lexid static-hyperenv] op))
    op))

(rc:ontype pk-parse-sip (lexid static-hyperenv)
             pk-sip-brackets pk-sip-brackets
  (zap car:rep self)
  (iflet (margin op rest) o-split-first-token.self
    (let op-fork (pk-parse op lexid static-hyperenv)
      (pk-fork-to-op op-fork rest lexid static-hyperenv))
    (do.fail "The syntax was an empty pair of brackets.")))

(rc:ontype pk-parse-sip (lexid static-hyperenv)
             pk-sip-hype-staticenv pk-sip-hype-staticenv
  (withs ((inner-lexid globalenv soup) rep.self
          tokens otokens.soup)
    (unless single.tokens
      (do.fail:+ "The syntax was a 'pk-sip-hype-staticenv without "
                 "exactly one word in it."))
    (let global-hyperenv (pk-make-hyperenv inner-lexid globalenv)
      (pk-parse car.tokens inner-lexid
        (pk-hyperenv-overlap global-hyperenv static-hyperenv)))))


(= pk-defuse-param* (dy.make-param [err:case type._ pk-native-err
                                     (error-message rep._.0)
                                     (tostring write._)]))

(def pk-defuse (body afterward)
  (pk-call afterward
    (catch:dy:param-let pk-defuse-param* [throw:pk-meta error list._]
      (pk-meta result pk-call.body))))

(def pk-err (contents)
  dy.param-get.pk-defuse-param*.contents)


(rc:ontype pk-call args fn fn
  ; NOTE: Jarc 17 treats escape continuations as errors, but we don't
  ; want to translate those into Penknife errors, since we're using
  ; escape continuations to implement 'pk-err in the first place.
  ; There doesn't seem to be an obvious way to throw arbitrary JVM
  ; exceptions in Jarc, so we exploit Jarc's mistreatment of escaped
  ; continuations here in order to throw a brand new
  ; jarc.lang$Continue value that happens to be an escape continuation
  ; with the same result as the original.
  (on-err (aif jv.jclass!jarc-lang$Continue
            [if (jv.ajava _ it)
              (catch.throw jvm!value._)
              (pk-err:annotate 'pk-native-err list._)]
            [pk-err:annotate 'pk-native-err list._])
          (thunk:apply self args)))

(rc:ontype pk-call args pk-fn-meta pk-fn-meta
  (pk-demeta:apply pk-call rep.self.0 args))

(rc:ontype pk-call args rc.list list
  (unless single.args
    (do.fail "A list takes one argument."))
  (self car.args))

(rc:ontype pk-call-set args rc.list list
  (unless single.args
    (do.fail "A list takes one argument."))
  [= (self car.args) _])

(rc:ontype pk-call-meta args pk-fn-meta pk-fn-meta
  (apply pk-call rep.self.0 args))

(rc:ontype pk-call-meta args rc.any rc.any
  (pk-meta result (apply pk-call self args)))


(mac def-pk-eval (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv fail)
                          ,@body)
       (,rc!ontype pk-eval-meta (lexid dyn-hyperenv) ,type ,type
         (pk-meta result
           (,g-backing-fn rep.self self lexid dyn-hyperenv fail)))
       (,rc!ontype pk-eval (lexid dyn-hyperenv) ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv fail)))))

(mac def-pk-eval-meta (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv fail)
                          ,@body)
       (,rc!ontype pk-eval-meta (lexid dyn-hyperenv) ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv fail))
       (,rc!ontype pk-eval (lexid dyn-hyperenv) ,type ,type
         (pk-demeta
           (,g-backing-fn rep.self self lexid dyn-hyperenv fail))))))

(def-pk-eval pk-lambdacalc-call
  (apply pk-call (map [pk-eval _ lexid dyn-hyperenv] self)))

(def-pk-eval pk-lambdacalc-call-set
  (apply pk-call-set (map [pk-eval _ lexid dyn-hyperenv] self)))

(def-pk-eval-meta pk-lambdacalc-call-meta
  (apply pk-call-meta (map [pk-eval _ lexid dyn-hyperenv] self)))

(def-pk-eval pk-lambdacalc-literal
  car.self)

(def-pk-eval-meta pk-lambdacalc-literal-meta
  car.self)

(def-pk-eval pk-lambdacalc-var
  (pk-dyn-hyperenv-get dyn-hyperenv self))

(def-pk-eval-meta pk-lambdacalc-var-meta
  (pk-dyn-hyperenv-get-meta dyn-hyperenv self))

(def-pk-eval pk-lambdacalc-set
  (pk-dyn-hyperenv-set
    dyn-hyperenv self.0 (pk-eval self.1 lexid dyn-hyperenv)))

(def-pk-eval pk-lambdacalc-set-meta
  (pk-dyn-hyperenv-set-meta
    dyn-hyperenv self.0 (pk-eval self.1 lexid dyn-hyperenv)))

(def-pk-eval pk-lambdacalc-demeta
  (pk-eval-meta car.self lexid dyn-hyperenv))

(def-pk-eval-meta pk-attached-lambdacalc
  (pk-eval-meta self.1 lexid self.0))

(def-pk-eval-meta pk-parse-fork
  (pk-eval-meta pk-fork-to-meta.tagged-self lexid dyn-hyperenv))

(def-pk-eval-meta pk-soup
  (pk-eval-meta (pk-parse tagged-self lexid dyn-hyperenv)
    lexid dyn-hyperenv))


; TODO: Figure out how global environments are going to work when
; loading from files.

(= pk-repllexid* 'pk-repllexid*)
(= pk-replenv* (pk-make-interactive-env))


; NOTE: In official Arc 3.1 and Anarki, the type of an exception is
; 'exception, but in Rainbow it's 'exn, and in Jarc 17 there is no Arc
; type; it's just a Java object.
(def error-message (error)
  (if (in type.error 'exception 'exn)
    details.error
      (jv.ajava error 'jarc.JarcError)
    jvm!getMessage.error
      ; Some Jarc errors are Errors from the JVM runtime itself, such
      ; as StackOverflowErrors and OutOfMemoryErrors. Jarc doesn't
      ; wrap these errors in anything, but it does let us catch them.
      (jv.ajava error 'java.lang.Throwable)
    (+ "" error)
    (err "The argument to 'error-message wasn't an error.")))

(def pktl (act-on report-error nextmeta)
  ; NOTE: Jarc's 'on-err suppresses escape continuations, so
  ; 'catch:until:on-err and 'throw would fail here.
  (car:catch:until:only.throw:on-err
    [do (do.report-error error-message._) nil]
    (thunk:let meta (iflet (meta) call.nextmeta
                      meta
                      (pk-meta action  (list:fn ())
                               quit    list!goodbye))
      (iflet (action) rep.meta!action
        pk-call.action
        do.act-on.meta)
      (whenlet (quit) rep.meta!quit
        list.quit))))

(def pktl-stream (lexid env str act-on report-error prompt)
  (zap newline-normalizer str)
  ; NOTE: If 'pk-staticenv-read-parse-tl raises an error while
  ; reading, rather than while parsing, this could loop infinitely. We
  ; plan to let the environment support command syntax we can't
  ; predict, such as multiple-word commands or commands with
  ; mismatched brackets, so there isn't an obvious way to separate the
  ; reading phase from the parsing phase.
  (let hyperenv (pk-make-hyperenv lexid env)
    (pktl act-on report-error
      (fn ()
        do.prompt.str     ; Wait for more input.
        (whenlet (expr) (pk-staticenv-read-parse-tl env lexid str)
          (list:pk-eval-meta expr lexid hyperenv))))))

; NOTE: Rainbow's profiler doesn't like function calls in optional
; arguments.
(w/uniq missing
  (def pkrepl ((o str missing))
    (when (is str missing)
      (= str (ut.xstdin)))
    (pktl-stream pk-repllexid* pk-replenv* str
      [let val pk-demeta._
        (on-err [prn "Error writing: " error-message._]
          (fn () write.val (prn)))]
      [prn "Error: " _]
      ; Show the prompt unless there's a non-whitespace character
      ; ready.
      [unless (catch:while rep._!ready
                (if (whitec rep._!peek)
                  rep._!read
                  throw.t))
        (pr "pk> ")])))

(def pkdo (lexid env str)
  ; Display no results, raise all errors, and show no prompts.
  ; NOTE: Rainbow doesn't like [].
  (pktl-stream lexid env str [do] err [do]))

(def pkload (lexid env filename)
  (w/infile str filename (pkdo lexid env str)))

; This is just a convenience for parsing things at the REPL.
(def pkparse (str)
  ; NOTE: Rainbow treats a&b.c as (andf a b.c).
  (pk-fork-to-get:pk-parse (start-word&finish-bracket-word str)
    pk-repllexid* (pk-make-hyperenv pk-repllexid* pk-replenv*)))
