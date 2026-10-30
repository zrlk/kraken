/-
**wake's value invariant with the second TCB's limit word pinned**
(AArch64): `GOf2 L m0`, the consumer's `GOf` (`FixG` at the first
TCB's limit word `pinA + 16`) with the second TCB's limit word
`lim2A L = pinA + lim2Off` also pinned, to its initial value or the limit
main's second `scc_rt_thread_init` stores there, `lim2V L` (the second
stack's base plus the guard). wake's second `scc_rt_alloc_tcb` takes the
header `8390915` (`movz #2307; movk #128, lsl #16`: `mOf = 2`) at
`scc_rt_pinned_next = 80` (`tcbLen`), so the header is `pinA + 96`, the
second TCB `pinA + 104` and its limit field `pinA + 112` (`lim2Off`, the one
place this offset is written). With it the child's prologue
bound (`Rt.PreChild.TcbArea.lim`) holds of every value the invariant allows.

- `lim2Off`, `lim2A`, `lim2V`, `GOf2`.
- `gOf2_ne`: off both limit words, any value; `gOf2_of`: `GOf` off the
  second limit word is `GOf2`; `gOf_of_gOf2`: `GOf2` is `GOf` with one more
  word pinned; `pin_ne2`.
- `gOf2_lim2V`, `gOf2_lim2`: the second limit word's values.
- `gOf2_lim2_le`: they are at most the second stack's base plus 4096, given
  the word's initial value is `0` (`hinit2`).
-/
import Spike.Lib.A64StartOfPlaceOK

namespace Spike.Lib.WakeGOf2

open Kraken Kraken.Promising
open Scc.Sem (FixG)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (GOf limW limV gOf_ne pin_ne)

/-- **The second TCB's limit word's offset** in the pinned region: the
header `pinA + 80 + 8·mOf` (`mOf 8390915 = 2`), the TCB one word on, its
field `1` one more. -/
abbrev lim2Off : BitVec 64 := 112#64

/-- **The second TCB's limit word** (`scc_rt_thread_init`'s field `1` of
the TCB `pinA + 104`). -/
abbrev lim2A (L : RuntimeLayout) : BitVec 64 := L.pinA + lim2Off

/-- **The limit main's second `scc_rt_thread_init` stores**: the second
stack's base plus the guard. -/
abbrev lim2V (L : RuntimeLayout) : Val := (L.stacksA + 16384#64 + 4096#64).setWidth 128

/-- **wake's runtime value invariant**: both TCBs' limit words hold their
initial value or their limit; any value elsewhere. -/
def GOf2 (L : RuntimeLayout) (m0 : Memory) : Loc → Val → Prop :=
  FixG [(limW L, limV L), ((lim2A L).toNat, lim2V L)] m0

variable {L : RuntimeLayout} {m0 : Memory}

/-- The second limit word is not the first. -/
theorem lim2_ne : lim2A L ≠ L.pinA + 16#64 := pin_ne (by decide)

/-- Off both limit words, any value. -/
theorem gOf2_ne {a : BitVec 64} (ha : a ≠ L.pinA + 16#64) (hb : a ≠ lim2A L) (v : Val) :
    GOf2 L m0 ⟨a, 8⟩ v := by
  unfold GOf2 FixG
  intro a' w hm hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  simp only [Loc.mk.injEq, and_true] at hl
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact (ha (by rw [hl]; simp only [limW, BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim
  · exact (hb (by rw [hl]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim

/-- **`GOf` off the second limit word is `GOf2`.** -/
theorem gOf2_of {l : Loc} {v : Val} (h : GOf L m0 l v) (hl : l ≠ ⟨lim2A L, 8⟩) : GOf2 L m0 l v := by
  unfold GOf2 FixG
  intro a w hm he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with hm | hm
  · exact h a w (by rw [hm]; exact List.mem_singleton_self _) he
  · simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    exact (hl (by rw [he]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim

/-- **`GOf2` is `GOf`** with one more word pinned. -/
theorem gOf_of_gOf2 {l : Loc} {v : Val} (h : GOf2 L m0 l v) : GOf L m0 l v := by
  unfold GOf FixG
  intro a w hm he
  exact h a w (List.mem_cons.mpr (.inl (List.mem_singleton.mp hm))) he

/-- A word `pinA + c` is the second limit word only at `c = lim2Off`. -/
theorem pin_ne2 {c : BitVec 64} (hc : c ≠ lim2Off) : L.pinA + c ≠ lim2A L :=
  fun h => hc ((BitVec.add_right_inj _).mp h)

/-- The second limit word may hold its limit. -/
theorem gOf2_lim2V : GOf2 L m0 ⟨lim2A L, 8⟩ (lim2V L) := by
  unfold GOf2 FixG
  intro a w hm he
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · have h := congrArg Loc.addr he
    simp only [limW, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact (lim2_ne (L := L) h).elim
  · exact .inl rfl

/-- **The second limit word's values**: its limit or its initial value. -/
theorem gOf2_lim2 {v : Val} (h : GOf2 L m0 ⟨lim2A L, 8⟩ v) : v = lim2V L ∨ v = m0.initVal ⟨lim2A L, 8⟩ :=
  h _ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- **The second limit word's values are at most the second stack's base
plus 4096**, given its initial value is `0`. -/
theorem gOf2_lim2_le (hinit2 : m0.initVal ⟨lim2A L, 8⟩ = 0) {v : Val} (h : GOf2 L m0 ⟨lim2A L, 8⟩ v) :
    (v.setWidth 64).toNat ≤ (L.stacksA + 16384#64).toNat + 4096 := by
  rcases gOf2_lim2 h with rfl | rfl
  · have := L.pool_fit
    obtain ⟨h1, h2⟩ := L.stacks_sub
    simp only at h1 h2
    simp only [lim2V, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hinit2]; simp

/-- info: 'Spike.Lib.WakeGOf2.gOf2_lim2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gOf2_lim2_le

end Spike.Lib.WakeGOf2
