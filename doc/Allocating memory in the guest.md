See src/emulator/memory.rs contains the low level methods for allocating memory in the guest and reading/writing to it.  Most of the time tests should use the higher level Guest trait described in [[Creating data structures in the guest]].

The `AutoGPtr` type is used to automatically free memory in the guest once it goes out of scope.  You almost always want to use this to manage allocated memory in your test.
