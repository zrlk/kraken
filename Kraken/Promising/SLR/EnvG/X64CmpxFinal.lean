/-
**The x64 `lock cmpxchg` spinlock on `EnvG`, unconditional**.

`X64CmpxPublic.x64_cmpx_counter_envG` takes the then-open chain link
`hchain : Theorem1FChain (I := isa) Arch.tso fuel` as a hypothesis. The
Theorem 1′ chain now carries a step guard and `Theorem1FChain` is a theorem
(`EnvG/RmwFailChain.lean`, `theorem1FChain`), so `x64_cmpx_counter_envG'`
is `x64_cmpx_counter_envG` with `hchain` discharged.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxPublic
import Kraken.Promising.SLR.EnvG.RmwFailChain

namespace Kraken.Promising.X64.EnvG.CmpxPublic

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG.Cmpx

/-- **`counter = N` for the x64 `lock cmpxchg` spinlock workers under
`Arch.tso`, on `EnvG`**, public form, **unconditional**: the statement of
`x64_cmpx_counter_envG` without `hchain` (discharged by `theorem1FChain`).
See `x64_cmpx_counter_envG` for the hypotheses and what is covered. -/
theorem x64_cmpx_counter_envG' [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxWorkerG)] {fuel : Nat}
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateC l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  x64_cmpx_counter_envG (theorem1FChain Arch.tso fuel) N l c hdisj hN32 hst hN hC0 hLk0 hc hf

#print axioms x64_cmpx_counter_envG'

end Kraken.Promising.X64.EnvG.CmpxPublic
