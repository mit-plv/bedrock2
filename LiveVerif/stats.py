# Processes output of `TIMED=1 make`, plain `make` won't work!
# Need to set
#   Ltac _stats := print_stats.
# in LiveProgramLogic.v before.

import sys
import os
import re

print_step_count = False

def print_table_line(current_file, func_count, snippet_count, linecount_of_file, step_count, secs, loop_count):
    if print_step_count:
        print(f"{current_file:<35} & {func_count:>5} & {snippet_count:>8} & {linecount_of_file:>5} & {step_count:>5} & {secs:>7} & {loop_count:>5} \\\\")
    else:
        print(f"{current_file:<35} & {func_count:>5} & {snippet_count:>8} & {linecount_of_file:>5} & {secs:>7} & {loop_count:>5} \\\\")

ignored_funcs = {
    'ring_buf_enq',
    'init_foo',
    'sll_prepend',
    'insert',
    'insertion_sort',
    'malloc_init',
    'malloc_node',
    'swap_16s',
    'strcmp',
    'init_baz',
    'init_sepapps',
    'init_baz',
    'init_bar',
    'strCmp',
    'swap_barAB',
}

counted_funcs = {
    'Malloc_init',
    'Malloc',
    'Free',
    'bst_init',
    'bst_alloc_node',
    'bst_add',
    'Memset',
    'cbt_init',
    'cbt_update_or_best',
    'cbt_best_leaf',
    'cbt_lookup',
    'cbt_alloc_leaf',
    'critical_bit',
    'cbt_insert_at',
    'cbt_insert',
    'Strcmp',
    'sll_reverse',
    'sll_inc',
    'u_min',
    'u_min3',
    'u_min3_alt',
    'malloc',
    'free',
    'sort3',
    'fibonacci',
    'bst_contains',
    'swap_bc',
    'swap_singleField',
    'swap',
    'swap_words',
    'swap_subarrays',
    'sort3_separate_args',
}

zero_loops = '-'

loop_counts = {
    'memset': '1+0',
    'convert_bytes_to_record': zero_loops,
    'swap': zero_loops,
    'swap_subarrays': zero_loops,
    'min': zero_loops,
    'sort3_separate_args': zero_loops,
    'swap_record_fields': zero_loops,
    'sort3': zero_loops,
    'fibonacci': '1+0',
    'onesize_malloc': '1+0',
    'linked_list': '1+1',
    'tree_set': '0+2',
    'critbit': '2+2',
    'nt_uint8_string': '0+1',
}

def linecount(path):
    with open(path, 'r') as fp:
        return len(fp.readlines())

def main():
    filepath = sys.argv[1]

    if not os.path.isfile(filepath):
        print("File path {} does not exist. Exiting...".format(filepath))
        sys.exit(1)

    current_file = ""
    current_func = ""
    linecount_of_file = 0
    func_count = 0
    step_count = 0
    snippet_count = 0
    secs = 0
    unclassified_funcs = []
    unknown_loop_counts = []

    print_table_line("File", "Funcs", "Snippets", "Lines", "Steps", "Time[s]", "Loops")
    print("\\hline")

    with open(filepath) as fp:
        for line in fp:
            line = line.rstrip()
            if current_file:
                m = re.match('^Stats: START "([^"]+)"', line)
                if m:
                    current_func = m.group(1)
                    if current_func in counted_funcs:
                        func_count += 1
                    else:
                        if not (current_func in ignored_funcs):
                            unclassified_funcs.append(current_func)
                        current_func = ""
                elif line == "Stats: STEP":
                    if current_func:
                        step_count += 1
                elif line == "Stats: SNIPPET":
                    if current_func:
                        snippet_count += 1
                else:
                    m = re.match(".*/" + current_file + ".vo .real: ([^ ,]+).*", line)
                    if m:
                        secs = m.group(1)
                        if func_count > 0:
                            name = f"\\lstinline|{current_file}|"
                            loop_count = loop_counts.get(current_file)
                            if loop_count == None:
                                loop_count = zero_loops
                                unknown_loop_counts.append(current_file)
                            print_table_line(name, func_count, snippet_count,
                                             linecount_of_file, step_count, secs,
                                             '$' + loop_count + '$')
                        current_file = ""
            else:
                m = re.match("^COQC (.*)", line)
                if m:
                    current_file_path = m.group(1)
                    m = re.match(".*/LiveVerifExamples/([^/]+).v", current_file_path)
                    if m:
                        current_file = m.group(1)
                        if (current_file.endswith("wip") or
                            current_file.endswith("old")):
                            current_file = ""
                        else:
                            linecount_of_file = linecount(current_file_path)
                            current_func = ""
                            func_count = 0
                            step_count = 0
                            snippet_count = 0
                            secs = 0
    if unclassified_funcs:
        print("Unclassified functions:")
        print(unclassified_funcs)

if __name__ == '__main__':
   main()
