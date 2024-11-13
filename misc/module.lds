SECTIONS {
 /DISCARD/ : {
  *(.discard)
  *(.discard.*)
 }
 __ksymtab 0 : { *(SORT(___ksymtab+*)) }
 __ksymtab_gpl 0 : { *(SORT(___ksymtab_gpl+*)) }
 __kcrctab 0 : { *(SORT(___kcrctab+*)) }
 __kcrctab_gpl 0 : { *(SORT(___kcrctab_gpl+*)) }
 .init_array 0 : ALIGN(8) { *(SORT(.init_array.*)) *(.init_array) }
 __jump_table 0 : ALIGN(8) { KEEP(*(__jump_table)) }
 __patchable_function_entries : { *(__patchable_function_entries) }
}
SECTIONS {
 .plt (NOLOAD) : { BYTE(0) }
 .got (NOLOAD) : { BYTE(0) }
 .got.plt (NOLOAD) : { BYTE(0) }
}
PROVIDE(__start_alloc_tags = 0);
PROVIDE(__stop_alloc_tags = 0);
