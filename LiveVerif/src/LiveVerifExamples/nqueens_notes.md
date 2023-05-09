Fig 2 by Filiatre with renamed variables, pc, and SSA:

```
int t(set avCols, set usedAsc, set usedDesc)
   // 0
   res := 1
   if avCols <> empty then
      av := (avCols \ usedAsc) \ usedDesc
      res := 0
      // 1
      while av <> emtpy do
         c := min_elt av
         tmp := t(avCols \ {c}, incrAll(usedAsc + {c}), decrAll(usedDesc + {c}))
         // 2
         res := res + tmp
         av := av \ {c}
   return res
```

implement recursion manually:


```
int queens(n)
   int res[n]
   int av[n]
   int c[n]
   set avCols[n]
   set usedAsc[n]
   set usedDesc[n]
   int pc[n]
   avCols[0] := 0..n-1
   usedAsc[0] := empty
   usedDesc[0] := empty
   pc[0] := 0
   signed depth := 0
   while depth >= 0:
      if pc[depth] == 0:
         res[depth] := 1
         if avCols[depth] <> empty then
            av[depth] := (avCols[depth] \ usedAsc[depth]) \ usedDesc[depth]
            res[depth] := 0
            pc[depth] := 1
      else if pc[depth] == 1:
         if av[depth] <> emtpy:
            c[depth] := min_elt av[depth]
            avCols[depth+1] := avCols[depth] \ c[depth]
            usedAsc[depth+1] := incrAll(usedAsc[depth] + {c[depth]})
            usedDesc[depth+1] := decrAll(usedDesc[depth] + {c[depth]})
            pc[depth] := 2
            depth := depth + 1
            pc[depth] := 0
         else:
            depth := depth - 1
      else if pc[depth] == 2:
         res[depth] := res[depth] + res[depth+1]
         av[depth] := av[depth] \ c[depth]
         pc[depth] := 1
   return res[0]
```


finding just one solution:
