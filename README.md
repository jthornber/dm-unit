# Introduction

Definition: By 'unit testing' I mean small, deterministic, tests of
small sections of code (eg, individual functions, or even individual
code paths within a function).

Given the repercussions of any bug in kernel code you'd think unit testing
would be common practice.  But most kernel testing tends to be performed
at the 'functional testing' level, ie. fire up the whole kernel and see
if it falls over.

I've unit tested the source code to our device-mapper targets in various ways
over the years:

- Maintaining similar user land libraries.

  This works well initially, but needs constant maintenance to ensure the
  library and upstream kernel code don't diverge.  Also, since the code
  is different, there is the question of how valid any test results are.

- Writing unit tests within a kernel module

  These test would then run automatically when the module is loaded.

  This works pretty well, but you are very restricted in what your test
  code can do.  For a start it must be written in C, you don't have access
  to common libraries, and you can't even call out to programs like 'diff' to
  verify results.

- Automatically extracting slices of C code.

  It's very hard to break dependencies in C code, which is why retrofitting unit
  tests to _any_ C project is difficult.

  I had a couple of attempts to write a tool that would extract vertical slices out
  of a C code base.  For instance if you wanted to unit test a particular function
  then you would slice that function and any other structs and functions that it used.
  Extracted structs would only contain the fields that were actually referenced by
  the testee.

   See [cslice2](https://github.com/jthornber/cslice2)


## dm-unit

Rather than testing the C source code, _dm-unit_ uses a tiny emulator
to test ordinary compiled modules.  Only the modules being tested are
loaded into the emulator; there is no need to build the full kernel.
No changes to the kernel code is neccessary.

Tests are written in Rust, which I find to be a big win given Rust is
a much higher level language than C.  Rust code can be injected at any
point allowing you to provide stubs for functions, trace calls, collect
statistics etc,.

The emulator has byte level permissions on memory, helping catch bugs.
For instance most dm-persistent-data tests make use of a stubbed version
of the block-manager code, which will make sure that data buffers returned
from a dm_bm_read_lock() are not writeable (something not possible in
the real kernel).

dm-unit speeds up development a *lot*, since my dev cycle is now:

- change kernel code
- compile module
- run dm-unit

Rather than:

- change kernel code
- build monolithic kernel
- Fire up a vm, passing the new kernel on the command line
- Run a test program within the vm, which will have to issue real io to generate the scenario.

# Documentation

The doc directory contains markdown files giving more information.  Best viewed in [Obsidian](https://obsidian.md).