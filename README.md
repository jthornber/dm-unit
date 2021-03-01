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



# Building the kernel modules

dm-unit emulates a 64bit Risc-V cpu, so you will need to set up a cross compile
environment.

Firstly install the riscv compiler and binutils.  For instance on Fedora:

```bash
dnf install binutils-riscv64-linux-gnu gcc-c++-riscv64-linux-gnu gcc-riscv64-linux-gnu
```

You then need to set a couple of environment variables:

```bash
export CROSS_COMPILE=riscv64-linux-gnu-
export ARCH=riscv
```

Where CROSS_COMPILE is the prefix to your riscv tools.  A quick way to do this is to
copy ./misc/setup-cross-compile to your kernel source dir, and source it before you
start work.

I recommend applying misc/disable-inlining.patch to your kernel if you are
doing development work.  It adds a config option to disable auto inlining.
Explict inline directives will still be obeyed.  Letting the compiler
choose which functions are inlined can be frustrating when something as
trivial as adding a printk to one function can cause a different function
to be inlined.  Inlined functions will not appear in the symbol table,
and cannot be hooked/tested.

```bash
patch -p1 < path/to/dm-unit/misc/disable-inlining.patch 
```

Now we need to configure your kernel.  Copy either misc/kernel.config or misc/no-inlining-kernel.config
to .config in your kernel source dir.

```bash
cp path/to/dm-unit/misc/no-inlining-kernel.config .config
```

Now you can build the modules:

```bash
make modules -j$(nproc)
```


# Building dm-unit

First install [rustup](https://rustup.rs/)

Then install the nightly tool chain:

```bash
rustup install nightly
```

The ./dm-unit script both builds and runs dm-unit.  This will take some time
the first time you run it as dependencies ('crates') are downloaded and built:

```bash
dm-unit -k path/to/kernel/source
```

# Running dm-unit

You must always specify the location of your kernel build using the -k parameter.  This
should be the root of your build tree, ie. if you specify FOO, then dm-unit will try and
load FOO/drivers/md/persistent-data/dm-persistent-data.ko.

Tests are named using a '/' separated set of identifiers, much like a file path.

eg,
```
pdata 
  block-manager 
    block-size .............................................. PASS
    create 
      nomem ................................................. PASS
      success ............................................... PASS
    nr-blocks ............................................... PASS
    read-lock ............................................... PASS
    write-lock .............................................. PASS
  btree 
    consume-cursor 
      empty-cursor-fails .................................... PASS
      multiple-entries ...................................... PASS
      one-entry ............................................. PASS
      two-entries ........................................... PASS
    del 
      empty ................................................. PASS
    insert-overwrite-lookup 
      ascending ............................................. PASS
      descending ............................................ PASS
      random ................................................ PASS
      runs .................................................. PASS
    redistribute-entries .................................... FAIL
There were failures.
Total tests: 16, Pass: 15, Fail: 1
```

The -t option can be used to select a subset of tests to run:

```
> ./dm-unit -k ../riscv-kernel/ -t cursor
pdata 
  btree 
    consume-cursor 
      empty-cursor-fails .................................... PASS
      multiple-entries ...................................... PASS
      one-entry ............................................. PASS
      two-entries ........................................... PASS
All tests passed: 4
```

Logging is controlled using the RUST_LOG environment variable, eg,

```
> export RUST_LOG=info
> ./dm-unit -k ../riscv-kernel/ -t runs
pdata 
  btree 
      insert-overtwrite-lookup 
[2021-03-01T10:27:00Z INFO  dm_unit::tests::btree] insert: residency = 85, instrs = 3394, read_locks = 2.6, write_locks = 2.2
[2021-03-01T10:27:05Z INFO  dm_unit::tests::btree] overwrite: residency = 85, instrs = 2606, read_locks = 2.5, write_locks = 2.2
[2021-03-01T10:27:07Z INFO  dm_unit::tests::btree] lookup: residency = 85, instrs = 1141, read_locks = 2.0, write_locks = 0.0
	    runs .................................................. PASS
    All tests passed: 1
```

The 'debug' logging level is very verbose, showing each instructions
executed by the emulator.  You may set log levels on a per code module
basis:

eg,
```
> export RUST_LOG=debug,dm_unit::vm=info
```


# Writing tests

## Example 1 - Forcing an error path





