import Spike.Lib.X64HelloRodataSrc

/-!
# `hello.w` on x86-64: rodata's buffer words and the buffer at the spawn

The source-only part of `Spike/Lib/A64HelloInst.lean` and the buffer definitions of `A64HelloClonePreH`
(`bufW`) and `A64HelloClonePreHOf` (`BufAtSpawn`), at the x86-64 source `X64HelloRodataSrc`:

* `bufW i`: the two lane words `wc_rodata` stores (`Hello1RodataSrc.rdK1`, `rdK2`);
* `BufAtSpawn s lb`: the latest source messages to `⟨lb, 0⟩`, `⟨lb, 1⟩` hold `bufW 0`, `bufW 1`, neither the
  last message (the shape of the buffer conjunct of the clone's precondition);
* `bufW_lt`, `bufBytes`, `bufBytes_utf8`: the words are `"Hello, world\n"`'s 13 bytes;
* `rodata_bufW`: rodata's lane stores are of `bufW 0`, `bufW 1`.

Unlike AArch64 (where `bufW` and `BufAtSpawn` sit with the clone's precondition, whose closure reaches the AArch64
syntax), they are stated here on the source alone, so that the x86-64 clone and instance modules share them.
-/

namespace Spike.Lib.X64HelloInst

open Scc.Sem.MemRel (SLatest)

/-- **Rodata's buffer words** (the two lane stores of `wc_rodata`). -/
def bufW (i : Nat) : Nat := if i = 0 then Spike.Lib.Hello1RodataSrc.rdK1 else Spike.Lib.Hello1RodataSrc.rdK2

theorem bufW_zero : bufW 0 = Spike.Lib.Hello1RodataSrc.rdK1 := rfl

theorem bufW_one : bufW 1 = Spike.Lib.Hello1RodataSrc.rdK2 := rfl

/-- **Rodata's buffer at the clone**: the latest source messages to `⟨lb, 0⟩`, `⟨lb, 1⟩` hold `bufW 0`,
`bufW 1`, neither the last message. -/
def BufAtSpawn (s : TermRun.Cfg) (lb : WeakMem.AllocLabel) : Prop :=
  ∀ i < 2, ∃ j m, SLatest s.mem ⟨lb, i⟩ j ∧ s.mem[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < s.mem.size

/-- The buffer's words are below `2^64`. -/
theorem bufW_lt (i : Nat) : bufW i < 2 ^ 64 := by
  unfold bufW; split <;> decide

/-- **The buffer's 13 bytes are `"Hello, world\n"`**: byte `k` is lane `k % 8` of word `k / 8`. -/
theorem bufBytes : (List.range 13).map (fun k => TermRun.laneN .w8 (bufW (k / 8)) (k % 8)) =
    [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10] := by decide

/-- The bytes are the UTF-8 of `"Hello, world\n"`. -/
theorem bufBytes_utf8 : "Hello, world\n".toUTF8.toList.map (·.toNat) =
    [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10] := by decide +kernel

/-- **rodata's lane words are the buffer's.** -/
theorem rodata_bufW :
    X64HelloRodataSrc.eW0 = .let_ "w0" (.asLanes false .w8 (.lit (bufW 0))) X64HelloRodataSrc.eO0 ∧
      X64HelloRodataSrc.eW1 = .let_ "w1" (.asLanes false .w8 (.lit (bufW 1))) X64HelloRodataSrc.eO1 :=
  ⟨rfl, rfl⟩

/-- `BufAtSpawn` is inhabited: the buffer's two words, then a third message elsewhere. -/
example : ∃ s lb, BufAtSpawn s lb := by
  refine ⟨{ mem := #[⟨⟨default, 0⟩, .num (bufW 0), default⟩, ⟨⟨default, 1⟩, .num (bufW 1), default⟩,
    ⟨⟨default, 2⟩, .num 0, default⟩], ths := #[] }, default, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => exact ⟨0, _, ⟨⟨_, rfl, rfl⟩, fun k m hk hm => by
      match k, hm with
      | 1, hm => cases hm; simp
      | 2, hm => cases hm; simp⟩, rfl, rfl, by decide⟩
  | 1, _ => exact ⟨1, _, ⟨⟨_, rfl, rfl⟩, fun k m hk hm => by
      match k, hm with
      | 2, hm => cases hm; simp⟩, rfl, rfl, by decide⟩

end Spike.Lib.X64HelloInst

