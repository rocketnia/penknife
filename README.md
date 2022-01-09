# Penknife Mk. I

[![CI](https://github.com/rocketnia/penknife/actions/workflows/ci.yml/badge.svg)](https://github.com/rocketnia/penknife/actions/workflows/ci.yml)

> ℹ️ If you're here, you might be interested in the newest incarnation of Penknife, which is in the [Era](https://github.com/era-platform/era) repository.

This implements the Penknife Mk. I programming language, a [Blade](https://github.com/rocketnia/blade)-like scripting language (which may mean nothing to you, since Blade is a vaporware hobby project ^\_^ ). Penknife, like Blade, is a language that emphasizes the use of whatever syntaxes the programmer finds best in every situation.

Unlike Blade, which statically compiles a directory structure, delaying compilation of certain declarations until the necessary syntaxes are known, Penknife interprets an ongoing character stream, invoking imperative commands one at a time to build up its definition space. This makes it suitable as a REPL language.

Penknife, like Blade, emphasizes a programming style by which convenient sub-languages are developed first, and then they're used to build data structures that are compiled into whatever performant or rigorous forms are necessary. A Penknife program may indeed have some behaviors in common with a build script, making system calls to invoke machine code compilers, archival utilities, documentation generators, and so forth—but without necessarily having any non-Penknife code in the project, instead generating that code as part of the build process.


## Installation and use

To use Penknife Mk. I, you'll need a working Arc setup (either official Arc (available via the [Anarki](https://arclanguage.github.io/) `official` branch), [Anarki](https://arclanguage.github.io/), [Jarc](http://jarc.sourceforge.net/), or [Rainbow](https://github.com/conanite/rainbow)), and you'll need to have the [Framewarc](https://github.com/rocketnia/framewarc) library. Note that Penknife is *extremely* slow on Jarc 17, and it's not actually a self-sufficient language on any of these platforms, since the global Penknife environment only has a few test functions and has neither a way to define new functions nor a way to run arbitrary Arc code. Right now, you're expected to implement those things yourself! It's an adventure~! :-p

The main entrypoint of the Penknife library is penknife.arc. To configure it to load files from a directory other than the working directory, set the global variable `penknife-dir*` before loading it, like so:

```racket
(= fwarc-dir* "my/path/to/framewarc/arc/")
(load:+ fwarc-dir* "loadfirst.arc")
(= penknife-dir* "my/path/to/penknife/")
(load:+ penknife-dir* "penknife.arc")
```

Framewarc must be loaded (as shown above) before loading penknife.arc. Mind the trailing slashes!

Once the library is loaded, you can use `(pkrepl)` to get to a Penknife REPL.

```racket
arc> (pkrepl)
pk> [+ arc["Hello, "] arc["world!"]]
"Hello, world!"
```

You can then use Ctrl+C or Ctrl+D to exit.


## Installation with npm

Penknife Mk. I is also available as an npm package. This may make it easier to install and automate its usage, despite the fact that it isn't a JavaScript library.

As an npm package, Penknife has no JavaScript functionality (so no `require("penknife-lang")`), but it does have a single piece of CLI functionality: The command `penknife-lang copy-into <path>` copies Penknife's Arc and Penknife source files into the directory at the given file path. This can be combined with the CLI functionality of [Rainbow.js](https://github.com/arclanguage/rainbow-js) and [Framewarc](https://github.com/rocketnia/framewarc) to build a host directory with Rainbow.js's core Arc libraries, Framewarc, and Penknife all in suitable places:

```bash
rainbow-js-arc init-arc my-arc-host-dir/
framewarc copy-into my-arc-host-dir/lib/framewarc/
penknife-lang copy-into my-arc-host-dir/lib/penknife/
```

Once you have these files in place, keep in mind that you'll still need to run the commands above to load Framewarc and Penknife and to start a Penknife REPL.

If you'd like to invoke the `penknife-lang copy-into <path>` command yourself from the command line, install Penknife globally:

```bash
npm install --global penknife-lang
```

If you'd just like to use it from your own package.json file's testing scripts, you can write the following to add it to your `devDependencies`:

```bash
npm install --save-dev penknife-lang
```
