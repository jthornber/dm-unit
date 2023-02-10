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
