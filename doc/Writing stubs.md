Stubs are used to override behaviour in the guest.  There are a couple of reasons why you would want to do this:

- Your module calls a core kernel function (eg, `kmalloc`), that is actually present in the vm.
- You wish to change the behaviour of some code.  eg, to force an error path.

## Providing an implementation for kmalloc

For instance, kmalloc is not present in modules, so we need to provide our own version:

``` Rust
pub fn kmalloc(fix: &mut Fixture) -> Result<()> {
    let len = fix.vm.reg(Reg::A0);
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0u8; len as usize], PERM_READ | PERM_WRITE)?;
    fix.vm.ret(ptr.0);
    Ok(())
}

fix.at_func("__kmalloc", Box::new(kmalloc))?;
```

The stub allocates some new memory in the guest, and returns _in the guest_ a pointer to this new memory.

## Stubs library

The `stubs` module provides a lot of sensible default implementations for core functions.  Often your test just needs to call `stubs::standard_globals(fix)` at the start.

## Forcing an error path

Consider this function:

``` C
static int split_one_into_two(struct shadow_spine *s, unsigned parent_index,
                              struct dm_btree_value_type *vt, uint64_t key)
{
        int r;
        struct dm_block *left, *right, *parent;
        struct btree_node *ln, *rn, *pn;
        __le64 location;

        left = shadow_current(s);

        r = new_block(s->info, &right);
        if (r < 0)
                return r;

        ln = dm_block_data(left);
        rn = dm_block_data(right);

        rn->header.flags = ln->header.flags;
        rn->header.nr_entries = cpu_to_le32(0);
        rn->header.max_entries = ln->header.max_entries;
        rn->header.value_size = ln->header.value_size;
        redistribute2(ln, rn);

        /* patch up the parent */
        parent = shadow_parent(s);
        pn = dm_block_data(parent);

        location = cpu_to_le64(dm_block_location(right));
        __dm_bless_for_disk(&location);
        r = insert_at(sizeof(__le64), pn, parent_index + 1,
                      le64_to_cpu(rn->keys[0]), &location);
        if (r) {
                unlock_block(s->info, right);
                return r;
        }

        /* patch up the spine */
        if (key < le64_to_cpu(rn->keys[0])) {
                unlock_block(s->info, right);
                s->nodes[1] = left;
        } else {
                unlock_block(s->info, left);
                s->nodes[1] = right;
        }

        return 0;
}
```

We'd like to have a unit test that exercises the error path when `insert_at` fails.  To do this we can either read the code for `insert_at`, work out when it fails, and then manipulate the vm to make these conditions happen.  Or, much easier, we can just replace `insert_at` with a stub that returns -ENOMEM:

``` Rust
￼pub fn no_mem(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(-ENOMEM);
    Ok(())
}

// Then in your test:
fix.at_func("insert_at", Box::new(no_mem))?;

// ... and call split_one_into_two() ...
```





