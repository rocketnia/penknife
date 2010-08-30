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
; mr   ; namespace of Lathe's multival/multirule.arc
; oc   ; namespace of Lathe's multival/order-contribs.arc
; rc   ; namespace of Lathe's orc/orc.arc
; sn   ; namespace of Lathe's imp/sniff.arc
; jv   ; namespace of Lathe's imp/jvm.arc
; plt  ; taken out of Lathe's imp/sniff.arc
; jvm  ; taken out of Lathe's imp/jvm.arc
;
; (thunk . body)  ; macro
;
; (fn-input-ify self)  ; rulebook
;
; (newline-normalizer str)
; (comment-ignorer str)
;
; (start-word str (o test ~whitec))
; (finish-bracket-word str (o test whitec))
; (finish-brackets str)
;
; (soup-whitec x)
; (orev self)                                     ; rulebook
; (o-ltrim self (o test soup-whitec))             ; rulebook
; (o-rtrim self (o test soup-whitec))             ; rulebook
; (o-split-first-token seq (o test soup-whitec))
; (o-split-last-token seq (o test soup-whitec))
; (otokens seq (o test soup-whitec))
; (slurp+ self other)                             ; rulebook
; (o+binary self other)                           ; rulebook
; (o+ first . rest)
; (soup->string soup)
; (slurp->string self)                            ; rulebook
; (soup->list soup)
; (slurp->list self)                              ; rulebook
; (pk-soup-singleton elem)
;
; (pk-fork-to-get self)                       ; rulebook
; (pk-fork-to-set self new-value)             ; rulebook
; (pk-fork-to-meta self)                      ; rulebook
; (pk-fork-to-op-method self)                 ; rulebook
; (pk-fork-to-op compiled-op body staticenv)
;
; (pk-compile-leaf-from-thunk staticenv getter)
; (pk-compile-literal-from-thunk compile-value staticenv)
; (pk-compile-call-from-thunk compile-op-and-body op-compiler)
; (pk-compile-fork-from-op op-compiler)
;
; (pk-function-call-compiler compiled-op body staticenv)
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
; (pk-staticenv-get-compile-fork self varname)  ; rulebook
; (pk-staticenv-default-op-compiler self)       ; rulebook
; (pk-staticenv-read-compile-tl self str)       ; rulebook
; (pk-staticenv-literal self name)              ; rulebook
; (pk-dynenv-ensure-binding self varname)       ; rulebook
; (pk-dynenv-get-binding self varname)          ; rulebook
; (pk-dynenv-get self varname)                  ; rulebook
; (pk-dynenv-get-meta self varname)             ; rulebook
; (pk-dynenv-set self varname)                  ; rulebook
; (pk-dynenv-set-meta self varname)             ; rulebook
;
; (pk-alpha-id-char x)
; (pk-infix-id-char x)
; (pk-string-identifier x)
; (pk-soup-identifier x)
; (pk-soup-compile-tl soup staticenv)  ; rulebook
; (pk-soup-compile soup staticenv)     ; rulebook
; (pk-sip-compile self staticenv)      ; rulebook
;
; (pk-call self . args)       ; rulebook
; (pk-call-set self . args)   ; rulebook
; (pk-call-meta self . args)  ; rulebook
;
; (def-pk-eval type . body)       ; macro
; (def-pk-eval-meta type . body)  ; macro
; (pk-eval self dynenv)           ; rulebook
; (pk-eval-meta self dynenv)      ; rulebook
; (pk-eval-tl self dynenv)        ; rulebook
;
; pk-replenv*  ; value of type 'pk-ad-hoc-env
;
; (error-message error)
; (pktl env str act-on report-error prompt)
; (pkrepl (o str (errsafe:stdin)))
; (pkdo env str)
; (pkload env filename)
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
; pk-soup-whitec
;   rep: Ignored. This value indicates a whitespace sip that doesn't
;        correspond to any particular character.
;
; pk-bracketed-soup
;   rep: A singleton proper list containing a value of type 'pk-soup.
;        This is soup which is semantically understood as being the
;        interior of a pair of brackets. It often appears as a sip in
;        another pk-bracketed-soup's soup in order to represent nested
;        brackets.
;
; pk-lambdacalc-literal
;   rep: A singleton list containing the value for this expression to
;        evaluate to.
;
; pk-lambdacalc-literal-meta
;   rep: A singleton list containing the metadata for this expression
;        to evaluate to.
;
; pk-lambdacalc-var
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression.
;
; pk-lambdacalc-var-meta
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression. This looks up
;        the 'pk-ad-hoc-meta metadata table corresponding to the
;        variable.
;
; pk-lambdacalc-set
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol representing the variable to modify in the
;             dynamic environment when evaluating this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will provide the new value for the variable
;             (which will also be the result of this expression). If
;             the new value has special metadata, that metadata will
;             be ignored, and it won't even be returned by this
;             expression.
;
; pk-lambdacalc-set-meta
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol representing the variable to modify in the
;             dynamic environment when evaluating this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will provide the new metadata for the
;             variable (and which will also be the non-metadata result
;             of this expression).
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
; pk-compile-fork
;   rep: A table which supports the following fields:
;   rep._!get:   A value which, when called using 'pk-call, accepts no
;                arguments and returns a value of one of the
;                'pk-lambdacalc-[something] types, representing an
;                expression that returns a value to be used in a
;                parent expression.
;   rep._!set:   A value which, when called using 'pk-call, accepts an
;                expression and returns another expression that sets
;                something to the value returned by the first
;                expression. Each of these expressions is a value of
;                one of the 'pk-lambdacalc-[something] types.
;   rep._!meta:  A value which, when called using 'pk-call, accepts no
;                arguments and returns a value of one of the
;                'pk-lambdacalc-[something] types, representing an
;                expression that returns a value to be used by a
;                top-level command interpreter.
;   rep._!op:    A value which, when called using 'pk-call or
;                'pk-call-meta, accepts this very 'pk-compile-fork
;                value (the compiled operator), a 'pk-soup value (the
;                uncompiled body), and a static environment and
;                returns a 'pk-compile-fork value representing the
;                compiled expression.
;
; pk-ad-hoc-binding
;   rep: A list which supports getting and setting the following
;        field:
;   rep._.0:  A value of type 'pk-ad-hoc-meta, representing the
;             metadata associated with the variable represented by
;             this binding.
;
; pk-ad-hoc-env
;   rep: A nullary function returning a table mapping bound variable
;        names to singleton proper lists containing their bindings.
;        The table returned is the same one each time, so that
;        'pk-dynenv-ensure-binding can mutate new bindings onto it.
;        The point of having this be a function, rather than just
;        being the table itself, is so that Jarc 17 and Rainbow don't
;        error out when trying to display an environment which has an
;        element that refers back to the same environment.
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
;   rep._!result:         The value to use as the result in any
;                         context other than the top-level one. This
;                         is the only non-optional field; if this is
;                         nil, then the value used is actually nil
;                         itself.
;   rep._!action:         If present, a singleton proper list
;                         containing a Penknife value which, when
;                         called with no arguments using 'pk-call,
;                         will imperatively perform some additional
;                         action which is meant to be done instead of
;                         writing the result to the REPL.
;   rep._!quit:           If present, a singleton proper list
;                         indicating that the Penknife REPL session
;                         should exit and return the contained value
;                         to the Arc REPL.
;   rep._!compile-fork:   If present, a singleton proper list
;                         containing a Penknife value which, when
;                         given a variable name as a string, will
;                         return the 'pk-compile-fork value to return
;                         when compiling an identification of the
;                         variable when treating an environment
;                         containing a binding with this meta-value as
;                         a static environment. If instead this is
;                         nil, then a default compile fork should be
;                         constructed according to that environment's
;                         own behavior.
;   rep._!error:          If present, the string to raise as an error
;                         message whenever the result, but not this
;                         metadata, is looked up in a binding or
;                         environment. If instead this is nil, then no
;                         error is raised.


(let lathe [+ lathe-dir* _ '.arc]
  (use-fromwds-as ut do.lathe!utils
                  mr do.lathe!multival/multirule
                  oc do.lathe!multival/order-contribs
                  rc do.lathe!orc/orc
                  oi do.lathe!orc/oiter
                  sn do.lathe!imp/sniff
                  jv do.lathe!imp/jvm))

(= plt sn.plt jvm jv.jvm)


(mac thunk body
  `(fn () ,@body))


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

(def comment-ignorer (str)
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
                             (is char #\;))
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


(def start-word (str (o test ~whitec))
  (zap testify test)
  (zap fn-input-ify str)
  (w/outstring s
    (catch:whilet char (or rep.str!peek rep.str!read)  ; Consume EOF.
      (if do.test.char
        (throw inside.s)
        (disp rep.str!read s)))))

(def finish-bracket-word (str (o test whitec))
  (zap testify test)
  (zap fn-input-ify str)
  (annotate 'pk-soup
    (accum acc
      (with (chars (outstring) nonchars nil)
        (while:caselet char (or rep.str!peek rep.str!read) #\[
          (do rep.str!read
              (only.acc:check inside.chars ~empty)
              (= chars (outstring))
              (push (annotate 'pk-bracketed-soup
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
  (case type.x char whitec.x rc.a-!pk-soup-whitec.x))

(rc:ontype orev () string string
  (tostring:down i (- len.self 1) 0
    (writec self.i)))

(rc:ontype o-ltrim ((o test soup-whitec)) rc.list list
  (aif (pos (complement testify.test) self)
    (split self it)
    (list self nil)))

(rc:ontype o-ltrim ((o test whitec)) string string
  (aif (pos (complement testify.test) self)
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

(def o-split-first-token (seq (o test soup-whitec))
  (zap testify test)
  (let (margin rest) (o-ltrim seq test)
    (awhen (check (o-ltrim rest ~test) ~oi.oempty:car)
      (cons margin it))))

(def o-split-last-token (seq (o test soup-whitec))
  (zap testify test)
  (let (rest margin) (o-rtrim seq test)
    (awhen (check (o-rtrim rest ~test) ~oi.oempty:cadr)
      (join it list.margin))))

(def otokens (seq (o test soup-whitec))
  (zap testify test)
  (accum acc
    (ut:dstwhilet (margin token rest) (o-split-first-token seq test)
      do.acc.token
      (= seq rest))))

; TODO: We should really use some kind of multiple dispatch for
; 'slurp+ and 'o+binary.

(rc:ontype slurp+ (other) rc.list list-and-list
  (unless (.other:rc.a- rc!list)
    (do.fail "The second argument didn't match the type \"list\"."))
  (list:+ self other))

(rc:ontype slurp+ (other) rc.list list-and-string
  (unless rc.a-!string.other
    (do.fail "The second argument didn't match the type \"string\"."))
  (list self other))

(rc:ontype slurp+ (other) string string-and-list
  (unless (.other:rc.a- rc!list)
    (do.fail "The second argument didn't match the type \"list\"."))
  (list self other))

(rc:ontype slurp+ (other) string string-and-string
  (unless rc.a-!string.other
    (do.fail "The second argument didn't match the type \"string\"."))
  (list:+ self other))

(rc:ontype o+binary (other) pk-soup pk-soup-and-pk-soup
  (unless rc.a-!pk-soup.other
    (do.fail:+ "The second argument didn't match the type "
               "\"pk-soup\"."))
  (if oi.oempty.self   other
      oi.oempty.other  self
    (withs (rep-self rep.self
            ; NOTE: Jarc is fine with (let (x (y)) z ...), but it
            ; doesn't allow (let ((x) y) z ...).
            (before (self-slurp))  (split rep-self (- len.rep-self 1))
            (other-slurp after)  (split rep.other 1))
      (zap car other-slurp)
      (annotate 'pk-soup
        (join before (slurp+ self-slurp other-slurp) after)))))

(def o+ (first . rest)
  (ut.foldl o+binary first rest))

(def soup->string (soup)
  ; NOTE: On Rainbow, (apply string '("something")) and
  ; (string '("something")) don't have the same result.
  (catch:apply string (map [or slurp->string._ throw.nil] rep.soup)))

(rc:ontype slurp->string () string string
  self)

(mr:rule slurp->string (self) default
  nil)

(oc:label-prefer-labels-last slurp->string-default-last
  'slurp->string 'default)

(def soup->list (soup)
  (catch:mappend [car:or slurp->list._ throw.nil] rep.soup))

(rc:ontype slurp->list () rc.list list
  list.self)

(mr:rule slurp->list (self) default
  nil)

(oc:label-prefer-labels-last slurp->list-default-last
  'slurp->list 'default)

; TODO: See how to make this aware of nonstandard kinds of slurps.
(def pk-soup-singleton (elem)
  (annotate 'pk-soup (list:.elem:case type.elem char string list)))


(rc:ontype pk-fork-to-get () pk-compile-fork pk-compile-fork
  (pk-call rep.self!get))

(rc:ontype pk-fork-to-set (new-value) pk-compile-fork pk-compile-fork
  (pk-call rep.self!set new-value))

(rc:ontype pk-fork-to-meta () pk-compile-fork pk-compile-fork
  (pk-call rep.self!meta))

(rc:ontype pk-fork-to-op-method () pk-compile-fork pk-compile-fork
  rep.self!op)

(def pk-fork-to-op (compiled-op body staticenv)
  (pk-call pk-fork-to-op-method.compiled-op
    compiled-op body staticenv))


(def pk-compile-leaf-from-thunk (staticenv getter)
  (zap memo getter)
  (annotate 'pk-compile-fork
    (obj get   getter
         set   [err:+ "An attempt was made to compile an ineligible "
                      "form for setting."]
         meta  getter
         op    pk-staticenv-default-op-compiler.staticenv)))

(def pk-compile-literal-from-thunk (compile-value staticenv)
  (pk-compile-leaf-from-thunk staticenv
    (thunk:annotate 'pk-lambdacalc-literal
      (list call.compile-value))))

(def pk-compile-call-from-thunk (compile-op-and-body op-compiler)
  (zap memo compile-op-and-body)
  (annotate 'pk-compile-fork
    (obj get   (memo:thunk:annotate 'pk-lambdacalc-call
                 call.compile-op-and-body)
         set   (let compile-set
                      (memo:thunk:annotate 'pk-lambdacalc-call-set
                        call.compile-op-and-body)
                 [annotate 'pk-lambdacalc-call
                   (list call.compile-set _)])
         meta  (memo:thunk:annotate 'pk-lambdacalc-call-meta
                 call.compile-op-and-body)
         op    op-compiler)))

(def pk-compile-fork-from-op (op-compiler)
  (fn (varname)
    (annotate 'pk-compile-fork
      (obj get   (thunk:annotate 'pk-lambdacalc-var varname)
           set   [annotate 'pk-lambdacalc-set (list varname _)]
           meta  (thunk:annotate 'pk-lambdacalc-var-meta varname)
           op    op-compiler))))


(def pk-function-call-compiler (compiled-op body staticenv)
  (pk-compile-call-from-thunk
    (thunk:cons pk-fork-to-get.compiled-op
      (map [pk-fork-to-get:pk-soup-compile _ staticenv]
           otokens.body))
    pk-staticenv-default-op-compiler.staticenv))


(mac pk-meta args
  `(annotate 'pk-ad-hoc-meta (obj ,@args)))

(def pk-demeta (meta)
  (only.err rep.meta!error)
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


(rc:ontype pk-staticenv-get-compile-fork (varname)
             pk-ad-hoc-env pk-ad-hoc-env
  (aif (aand (pk-dynenv-get-binding self varname)
             (!compile-fork:rep:pk-binding-get-meta car.it))
    (pk-call car.it varname)
    (let op-compiler pk-staticenv-default-op-compiler.self
      (pk-call pk-compile-fork-from-op.op-compiler varname))))

(rc:ontype pk-staticenv-default-op-compiler ()
             pk-ad-hoc-env pk-ad-hoc-env
  pk-function-call-compiler)

; TODO: Allow read behavior customization among 'pk-ad-hoc-env values.
(rc:ontype pk-staticenv-read-compile-tl (str)
             pk-ad-hoc-env pk-ad-hoc-env
  (aif (start-word&finish-bracket-word comment-ignorer.str)
    (pk-soup-compile-tl it self)
    (annotate 'pk-lambdacalc-literal-meta
      (list:pk-meta action (list:fn ()) quit list!goodbye))))

; TODO: Allow literal syntax customization among 'pk-ad-hoc-env
; values.
(rc:ontype pk-staticenv-literal (name) pk-ad-hoc-env pk-ad-hoc-env
  (zap [string:or _ "nil"] name)
  (when (all digit name)
    (list int.name)))

; TODO: Figure out how best to make this thread-safe.
; TODO: See if the name ought to be baked into the metadata this way.
(rc:ontype pk-dynenv-ensure-binding (varname)
             pk-ad-hoc-env pk-ad-hoc-env
  (car:or= (.varname:rep.self)
    (list:pk-make-ad-hoc-binding-meta:pk-meta error
      (+ "The variable \"" (or varname "nil") "\" is unbound."))))

(rc:ontype pk-dynenv-get-binding (varname) pk-ad-hoc-env pk-ad-hoc-env
  (.varname:rep.self))

(rc:ontype pk-dynenv-get (varname) pk-ad-hoc-env pk-ad-hoc-env
  (pk-binding-get:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-get-meta (varname) pk-ad-hoc-env pk-ad-hoc-env
  (pk-binding-get-meta:pk-dynenv-ensure-binding self varname))

(rc:ontype pk-dynenv-set (varname new-value)
             pk-ad-hoc-env pk-ad-hoc-env
  (pk-binding-set (pk-dynenv-ensure-binding self varname) new-value))

(rc:ontype pk-dynenv-set-meta (varname new-value)
             pk-ad-hoc-env pk-ad-hoc-env
  (pk-binding-set-meta
    (pk-dynenv-ensure-binding self varname) new-value))


; For efficiency, this assumes the argument is a character.
(def pk-alpha-id-char (x)
  (or alphadig.x (pos x "+-*/<=>") (< 255 int.x)))

; For efficiency, this assumes the argument is a character.
(def pk-infix-id-char (x)
  (~or pk-alpha-id-char.x (<= int.x 32)))

(def pk-string-identifier (x)
  (case type.x string
    (when (or (all pk-alpha-id-char x) (all pk-infix-id-char x))
      (list sym.x))))

(def pk-soup-identifier (x)
  (case type.x pk-soup (only.pk-string-identifier soup->string.x)))

(mr:rule pk-soup-compile-tl (soup staticenv) expression
  (pk-fork-to-meta:pk-soup-compile soup staticenv))

(mr:rule pk-soup-compile (soup staticenv) one-sip
  (iflet (sip) (and (oi.olen< soup 2)
                    (no soup->string.soup)
                    soup->list.soup)
    (pk-sip-compile sip staticenv)
    (do.fail "The word wasn't simply a single non-character.")))

(mr:rule pk-soup-compile (soup staticenv) identifier
  (iflet (name) pk-soup-identifier.soup
    (iflet (literal) (pk-staticenv-literal staticenv name)
      (pk-compile-literal-from-thunk thunk.literal staticenv)
      (pk-staticenv-get-compile-fork staticenv name))
    (do.fail "The word wasn't an identifier.")))

(mr:rule pk-soup-compile (soup staticenv) infix
  (iflet (left op right) (o-split-last-token soup
                           [~case type._ char pk-infix-id-char._])
    (if oi.oempty.left
      (do.fail:+ "The word started with its only infix operator, so "
                 "it wasn't an infix form.")
      (ut:lets it (pk-soup-compile op staticenv)
               it (pk-fork-to-op it left staticenv)
                  (pk-fork-to-op it right staticenv)))
    (do.fail "The word didn't contain an infix operator.")))

(mr:rule pk-soup-compile (soup staticenv) prefix
  (let (op bodies) (o-rtrim soup rc.a-!pk-bracketed-soup)
    (unless (or (and oi.oempty.op (oi.olen> bodies 1))
                (and pk-soup-identifier.op (oi.olen> bodies 0)))
      (do.fail:+ "The word wasn't a series of bracketed bodies "
                 "preceded by a bracket form or an identifier."))
    (zap soup->list bodies)
    (= op (if oi.oempty.op
            (pk-sip-compile pop.bodies staticenv)
            (pk-soup-compile op staticenv)))
    (each body (map car:rep bodies)
      (zap [pk-fork-to-op _ body staticenv] op))
    op))

(rc:ontype pk-sip-compile (staticenv)
             pk-bracketed-soup pk-bracketed-soup
  (zap car:rep self)
  (iflet (margin op rest) o-split-first-token.self
    (pk-fork-to-op (pk-soup-compile op staticenv) rest staticenv)
    (do.fail "The syntax was an empty pair of brackets.")))


(rc:ontype pk-call args fn fn
  (apply self args))

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

(mr:rule pk-call-meta (op . args) default
  (pk-meta result (apply pk-call op args)))

(oc:label-prefer-labels-last pk-call-meta-default-last
  'pk-call-meta 'default)


(mac def-pk-eval (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self dynenv fail) ,@body)
       (,rc!ontype pk-eval-meta (dynenv) ,type ,type
         (pk-meta result (,g-backing-fn rep.self self dynenv fail)))
       (,rc!ontype pk-eval (dynenv) ,type ,type
         (,g-backing-fn rep.self self dynenv fail)))))

(mac def-pk-eval-meta (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self dynenv fail) ,@body)
       (,rc!ontype pk-eval-meta (dynenv) ,type ,type
         (,g-backing-fn rep.self self dynenv fail))
       (,rc!ontype pk-eval (dynenv) ,type ,type
         (pk-demeta (,g-backing-fn rep.self self dynenv fail))))))

(def-pk-eval pk-lambdacalc-call
  (apply pk-call (map [pk-eval _ dynenv] self)))

(def-pk-eval pk-lambdacalc-call-set
  (apply pk-call-set (map [pk-eval _ dynenv] self)))

(def-pk-eval-meta pk-lambdacalc-call-meta
  (apply pk-call-meta (map [pk-eval _ dynenv] self)))

(def-pk-eval pk-lambdacalc-literal
  car.self)

(def-pk-eval-meta pk-lambdacalc-literal-meta
  car.self)

(def-pk-eval pk-lambdacalc-var
  (pk-dynenv-get dynenv self))

(def-pk-eval-meta pk-lambdacalc-var-meta
  (pk-dynenv-get-meta dynenv self))

(def-pk-eval pk-lambdacalc-set
  (pk-dynenv-set dynenv self.0 (pk-eval self.1 dynenv)))

(def-pk-eval pk-lambdacalc-set-meta
  (pk-dynenv-set-meta dynenv self.0 (pk-eval self.1 dynenv)))

(def-pk-eval pk-lambdacalc-demeta
  (pk-eval-meta car.self dynenv))

(rc:ontype pk-eval (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval pk-fork-to-get.self dynenv))

(rc:ontype pk-eval (env) pk-soup pk-soup
  (pk-eval (pk-soup-compile self env) env))

(rc:ontype pk-eval-meta (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval-meta pk-fork-to-meta.self dynenv))

(rc:ontype pk-eval-meta (env) pk-soup pk-soup
  (pk-eval-meta (pk-soup-compile self env) env))

(rc:ontype pk-eval-tl (env) pk-soup pk-soup
  (pk-eval-meta (pk-soup-compile-tl self env) env))


; TODO: Figure out how global environments are going to work when
; loading from files.

(= pk-replenv* (let rep (table) (annotate 'pk-ad-hoc-env thunk.rep)))


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

(def pktl (env str act-on report-error prompt)
  (zap newline-normalizer str)
  ; NOTE: Jarc's 'on-err suppresses escape continuations, so
  ; 'catch:until:do and 'throw would fail here.
  (car:catch:until:only.throw:do
    prompt.str                    ; Wait for more input.
    (let expr (pk-staticenv-read-compile-tl env str)
      (on-err [do (do.report-error error-message._) nil]
        (thunk:let meta (pk-eval-meta expr env)
          (iflet (action) rep.meta!action
            pk-call.action
            do.act-on.meta)
          (whenlet (quit) rep.meta!quit
            list.quit))))))

; NOTE: On Rainbow, (stdin), of all things, produces an error. When
; that happens, we go get it ourselves.
(def pkrepl ((o str (errsafe:stdin)))
  (when (and no.str jv.jclass!rainbow-functions-IO)
    (= str (jvm!rainbow-functions-IO-stdIn)))
  (pktl pk-replenv*
        str
        [on-err [prn "Error writing: " error-message._]
          (fn () (write pk-demeta._) (prn))]
        [prn "Error: " _]
        ; Show the prompt unless there's a non-whitespace character
        ; ready.
        [unless (catch:while rep._!ready
                  (if (whitec rep._!peek)
                    rep._!read
                    throw.t))
          (pr "pk> ")]))

(def pkdo (env str)
  ; Don't display any results, raise all errors, and don't show any
  ; prompts.
  (pktl env str [do] err [do]))

; NOTE: Rainbow doesn't like [].
(def pkload (env filename)
  (w/infile str filename (pkdo env str)))
