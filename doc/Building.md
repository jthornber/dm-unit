To run the tests you need to build dm-unit and you must build the kernel module that you wish to test.


## Building the kernel modules

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

Apply this patch misc/all.patch to your kernel.  Among other things it
adds a config option to disable auto inlining.
Explict inline directives will still be obeyed.  Letting the compiler
choose which functions are inlined can be frustrating when something as
trivial as adding a printk to one function can cause a _different_ function
to be inlined.  Inlined functions will not appear in the symbol table,
and cannot be hooked/tested.

```bash
patch -p1 < path/to/dm-unit/misc/all.patch 
```

Now we need to configure your kernel.  Copy either misc/kernel.config or misc/no-inlining-kernel.config
to .config in your kernel source dir.

```bash
cp path/to/dm-unit/misc/no-inlining-kernel.config .config
```

If you configure by hand be sure to disable any stack protection.
It's not needed and uses the thread pointer register which dm-unit
doesn't set up.

Now you can build the modules:

```bash
make modules -j$(nproc)
```

You do not need to build the main kernel image (vmlinux).


## Building dm-unit

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
