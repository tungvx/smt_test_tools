\ Model main
\ LP format - for model browsing. Use MPS format to capture full model detail.
Minimize
  0 C0 + 0 C1
Subject To
 R0: C3 <= -1
 R1: C2 - C3 <= -1
Bounds
 C0 free
 C1 free
 C2 free
 C3 free
End
