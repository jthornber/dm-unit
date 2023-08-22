It's common to write wrappers for the api that you are testing to make calling into the guest easy.  Examples can be found within src/wrappers.  Here are some snippets from the wrappers for the code in drivers/md/persistent-data/dm-btree.[hc].

## dm_btree_empty()

First we write a little utility to create a btree_info object in the guest with scoped lifetime.

``` Rust
pub fn auto_info<'a, G: Guest>(
    fix: &'a mut Fixture,
    info: &BTreeInfo<G>,
) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest(&mut fix.vm.mem, info, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}
```

Now we write a wrapper for dm_btree_empty.

``` C
int dm_btree_empty(struct dm_btree_info *info, dm_block_t *root);
```

We need to pass two arguments:
- the guest ptr to the btree info object
- a pointer for the result

It returns an integer error code as is typical for kernel code, we promote any errors to Rust Results by using the `fix.call_with_errno()` method.

Finally the result is read out of the `root` pointer that we allocated.

``` Rust
pub fn dm_btree_empty<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;

    fix.vm.set_reg(A0, info_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_btree_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}
```

## dm_btree_insert()

``` C
int dm_btree_insert(struct dm_btree_info *info, dm_block_t root,
                    uint64_t *keys, void *value, dm_block_t *new_root)
                    __dm_written_to_disk(value);
```

`dm_btree_insert` has more arguments, but is implemented in exactly the same way.

``` Rust
pub fn dm_btree_insert<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
    v: &G,
) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    let (mut fix, guest_keys) = auto_keys(&mut *fix, keys)?;
    let (mut fix, guest_value) = auto_guest(&mut *fix, v, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut *fix, 8)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, guest_keys.0);
    fix.vm.set_reg(A3, guest_value.0);
    fix.vm.set_reg(A4, new_root.0);

    fix.call_with_errno("dm_btree_insert")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    Ok(new_root)
}
```
