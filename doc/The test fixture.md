Every test will have a _fixture_ object passed into it:

``` Rust
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
	...
}
```

This object contains:
 - an emulator that will run the kernel code.  Access the emulator via the `fix.vm` field.  This emulator is freshly set up for each test, it will only contain the kernel modules that were requested when the test was registered.
 - A symbol table mapping guest symbol names to guest addresses.
 - A list of breakpoints.  Associated with each breakpoint is a Rust callback that is called whenever the emulator hits the breakpoint.  This is how we inject test specific code into the kernel modules.
 

