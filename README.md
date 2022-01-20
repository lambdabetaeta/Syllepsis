# Syllepsis

A proof of _syllepsis_, i.e. the statement that for any type `X`, point `a : X`, and 2-loops `p, q : idpath (idpath a) = idpath (idpath a)` we have

```
EH p q @ EH q p = 1
```

where `EH` is the proof of Eckmann-Hilton. The proof uses the Coq HoTT library.
