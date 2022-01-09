; penknife.arc


; Copyright (c) 2010, 2022 Rocketnia
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


; This is just a loader file. For a better description of what
; Penknife is, see pk-core.arc.
;
; To configure this loader to load files from a directory other than
; the working directory, set the global variable 'penknife-dir* before
; loading this, like so:
;
;   (= fwarc-dir* "my/path/to/framewarc/arc/")
;   (load:+ fwarc-dir* "loadfirst.arc")
;   (= penknife-dir* "my/path/to/penknife/")
;   (load:+ penknife-dir* "penknife.arc")
;
; Framewarc must be loaded (as shown above) before loading this file.
; Mind the trailing slashes!

(let penknife-dir (or global!penknife-dir* "")
  (each file '(pk-core pk-util pk-thin-fn pk-hefty-fn pk-qq)
    (load:+ penknife-dir file '.arc))
  (pkload pk-replenv* (+ penknife-dir 'pk-util.pk)))
