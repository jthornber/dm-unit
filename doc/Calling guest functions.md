The fixture provides a couple of methods that make a call into the guest, _call()_ and _call_with_errno()_.

When these are called the fixture looks up the symbol to get a guest address, sets the guest program counter to that address and runs the emulator.  When the called function completes, control returns to the rust program.

## Passing arguments

To pass arguments to the guest function you must set up the argument registers in the emulator.  These are named A0, A1 ...

For example to pass 2 arguments to a function containing 1234 and 0:
``` Rust
	fix.vm.set_reg(A0, 1234);
	fix.vm.set_reg(A1, 0);
```

## Retrieving the result

The return value from a guest function will be held in the A0 register:

``` Rust
	let result = self.vm.reg(A0);
```

With kernel code we often return a non zero integer to indicate an error.  The `fix.call_with_errno()` function automatically retrieves this error code and returns a Result::Err() value if it's non zero.

## Wrappers

Rather than making these calls directly in your test code it's easiest to write Rust functions that wrap the api that you're trying to test.

For example, to wrap this kernel function:

``` C
int dm_btree_empty(struct dm_btree_info *info, dm_block_t *root);
```

We write:

``` Rust
pub fn dm_btree_empty<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;

    fix.vm.set_reg(A0, info_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_btree_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}
```

The _info_ parameter contains a description of the btree.  We move it into guest memory, giving us _info_ptr_ which is a pointer to guest.  This pointer is then set as the first argument using set_reg.  We then allocate a block of guest memory to hold the pointer _root_, and set this as the second argument.

The call is then made.

Finally we read the pointer _root_ out of guest memory and return it.

See [[Allocating memory in the guest]] for more on memory management.
See `src/wrappers/*` for many more examples.