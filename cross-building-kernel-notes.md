There are two variables to set.  ARCH should always be 'riscv'.  CROSS_COMPILE should be a prefix
for your riscv toolset, this may include the full path (eg, riscv64-linux-gnu-).

To get a basic config:

	make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- defconfig
	
To build dm modules:

	make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- modules

Easiest to set these vars in a shell script and source.
