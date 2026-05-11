pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use type Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

package body Ring_Buffer with SPARK_Mode => On is

   function Is_Valid (B : Buffer) return Boolean
   is (Capacity_Is_Not_Too_Large (B.Capacity)
     and then B.Read < B.Capacity + B.Capacity
     and then B.Write < B.Capacity + B.Capacity
     and then Length (B) <= B.Capacity);

   function Capacity_Is_Not_Too_Large (C : Capacity_Type) return Boolean
   is (C <= Natural'Last - C
     and then 2 * C - 1 <= Natural'Last - 2 * C);

   function Buffer_Init (Capacity : Capacity_Type) return Valid_Buffer is
      Buffer_Empty : constant Buffer :=
        (Capacity => Capacity,
         Memory   => [others => Uninit],
         Read     => 0,
         Write    => 0);
   begin
      return Buffer_Empty;
   end Buffer_Init;

   function Mask (B : Valid_Buffer; I : Natural) return Positive
   is (1 + I mod B.Capacity);

   function Length (B : Buffer) return Natural
   is
      Read : constant Integer := B.Read mod (2 * B.Capacity);
      Write : constant Integer := B.Write mod (2 * B.Capacity);
      Rs : constant Big_Integer := To_Big_Integer (B.Read);
      Ws : constant Big_Integer := To_Big_Integer (B.Write);
      R : constant Big_Integer := To_Big_Integer (Read);
      W : constant Big_Integer := To_Big_Integer (Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin
      --  Note that our buffer isn't known to be valid, but we want to
      --  be working with read and write indices mod 2C, so we must
      --  show that this is equivalent.
      Lemma_Mod_Idempotent (Rs, 2 * C);
      Lemma_Mod_Idempotent (Ws, 2 * C);
      --  With unbounded indices W*, R*, and W, R both defined mod 2C,
      --  we show W* - R* ≡ W - R mod 2C.
      --  (First, W* - R* ≡ W - R* mod 2C)
      Lemma_Mod_Trans_Compat (Ws, W, -Rs, 2*C);
      --  (Next, W - R* ≡ W - R mod 2C)
      Lemma_Mod_Trans_Compat (-Rs, -R, W, 2*C);
      Lemma_Mod_Scale_Compat (Rs, R, -1, 2*C);
      --  Computing length, we add 2C to avoid overflow.
      Lemma_Mod_Trans_Compat (To_Big_Integer (0), 2 * C, W - R, 2 * C);
      return ((2 * B.Capacity + Write) - Read) mod (2 * B.Capacity);
   end Length;

   function Is_Empty (B : Valid_Buffer) return Boolean is
      N : constant Big_Integer := To_Big_Integer (Length (B));
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin
      --  This direction is trivial
      pragma Assert (if B.Read = B.Write then Length (B) = 0);

      --  The other requires some modular arithmetic lemmas. By
      --  assumption, our length N ≡ W - R mod 2C. When N is zero, we
      --  have 0 ≡ W - R mod 2C, so W ≡ R mod 2C.
      Lemma_Mod_Trans_Compat (N, W - R, R, 2*C);
      --  Since both 0 <= W, R < 2C, mod does nothing and W = R.
      Lemma_Mod_Nop (R, 2*C);
      Lemma_Mod_Nop (W, 2*C);

      return B.Read = B.Write;
   end Is_Empty;

   function Is_Full (B : Valid_Buffer) return Boolean
   is (Length (B) = B.Capacity);

   function Get (B : Valid_Buffer; I : Natural) return Element is
   begin
      return B.Memory (Mask (B, B.Read + I));
   end Get;

   procedure Push (B : in out Valid_Buffer; V : Element) is
      procedure Lemma_Pushed_Element_At_Back (R, W, N, C : Big_Integer)
        with Ghost,
             Pre => (0 <= R and then R < 2 * C) and then (0 <= W and then W < 2 * C)
                    and then (0 <= N and then N < C)
                    and then N = (W - R) mod (C*2),
             Post => W mod C = (R + N) mod C
      is
      begin
         --  We know
         --      N ≡ W - R  mod 2C
         --  R + N ≡ W      mod 2C
         --  And this is still congruent mod C. This matches the form
         --  that Mask returns (R + index), so the element at the masked
         --  index R + N is exactly V.
         Lemma_Mod_Trans_Compat (N, W - R, R, 2*C);
         --  pragma Assert (W mod (2*C) = (R + N) mod (2*C));
         Lemma_Mod_Composite (W, R + N, 2, C);
         pragma Assert (W mod C = (R + N) mod C);
      end Lemma_Pushed_Element_At_Back;

      procedure Lemma_Front_Distinct_From_Pushed (R, W, N, C, I : Big_Integer)
        with Ghost,
             Pre => (0 <= R and then R < 2 * C) and then (0 <= W and then W < 2 * C)
                    and then (0 <= N and then N < C)
                    and then N = (W - R) mod (C*2)
                    and then (0 <= I and then I < N),
             Post => (R + I) mod C /= (R + N) mod C
      is
      begin
         Lemma_Mod_Nop (I, C);
         Lemma_Mod_Nop (N, C);
         Lemma_Mod_Trans_Compat (I, N, R, C);
      end Lemma_Front_Distinct_From_Pushed;

      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
      N : constant Big_Integer := To_Big_Integer (Length (B));
      Np : constant Big_Integer := ((W + 1) mod (2*C) - R) mod (2*C);
      Write : constant Natural := B.Write;
      OldB : constant Valid_Buffer := B;
      NewB : Buffer := B;

   begin

      NewB.Memory (Mask (B, B.Write)) := V;
      NewB.Write := (B.Write + 1) mod (2 * B.Capacity);

      --  Proof that the length increments:
      Lemma_Push_Increases_Length (R, W, C, N, Np, 1);

      --  Proof that the new buffer is valid:
      pragma Assert (Is_Valid (NewB));
      B := NewB;

      --  Proof that the element we added is in the right place:
      Lemma_Pushed_Element_At_Back (R, W, N, C);
      pragma Assert (Mask (B, Write) = Mask (B, B.Read + (Length (B) - 1)));

      --  Proof that all the old elements are unchanged:
      for I in 0 .. Length (OldB) - 1 loop
         --  No index overlaps with where V is.
         Lemma_Front_Distinct_From_Pushed (R, W, N, C, To_Big_Integer (I));
         pragma Assert (Mask (B, B.Read + I) /= Mask (B, B.Read + Length (OldB)));

         --  Read index is unchanged, and we haven't written to this
         --  place, so the elements are unchanged.
         pragma Assert (Get (B, I) = Get (OldB, I));

         --  Induct over this.
         pragma Loop_Invariant ((for all K in 0 .. I => Get (OldB, K) = Get (B, K)));
      end loop;

   end Push;

   procedure Pop (B : in out Valid_Buffer; V : out Element) is
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
      N : constant Big_Integer := To_Big_Integer (Length (B));
      Rp : constant Big_Integer := (R + 1) mod (2*C);
      Np : constant Big_Integer := (W - Rp) mod (2*C);
      OldB : constant Valid_Buffer := B;
      NewB : Buffer := B;
   begin
      V := B.Memory (Mask (B, B.Read));
      NewB.Read := (B.Read + 1) mod (2 * B.Capacity);

      --  Proof that the length decrements:
      Lemma_Pop_Decreases_Length (R, W, C, N, Np, 1);

      --  Proof that the new buffer is valid:
      pragma Assert (Is_Valid (NewB));
      B := NewB;

      --  Proof that pop leaves back elements unchanged:
      pragma Assert (Length (B) < Length (OldB));
      for I in 0 .. Length (B) - 1 loop
         Lemma_Pop_Shifts_Back_Elements (R, Rp, C, To_Big_Integer (I), 1);
         pragma Assert (Get (B, I) = Get (OldB, I + 1));

         --  Induct on it.
         pragma Loop_Invariant ((for all K in 1 .. I => Get (B, K) = Get (OldB, K + 1)));
      end loop;
   end Pop;

   procedure Clear (B : in out Valid_Buffer) is
   begin
      B.Write := B.Read;
   end Clear;

   procedure Truncate_Back (B : in out Valid_Buffer; To_Length : Natural) is
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
      N : constant Big_Integer := To_Big_Integer (Length (B));
      L : constant Big_Integer := To_Big_Integer (To_Length);
      Rp : constant Big_Integer := (W - L) mod (2*C);
      Np : constant Big_Integer := (W - Rp) mod (2*C);
      dR : constant Big_Integer := N - L;
      OldN : constant Natural := Length (B);
      OldB : constant Valid_Buffer := B;
      NewB : Buffer := B;
   begin
      if To_Length < Length (B) then
         NewB.Read := (B.Write - To_Length) mod (2 * B.Capacity);

         --  Proof that the new length is L:
         --  Must prove that Np = (W - (R + dR) mod 2C) mod 2C to use our lemma.
         --  It suffices to show that Rp = (R + dR) mod 2C, by our definition for Np.
         --  We set Rp = W - L mod 2C, so
         --  Rp ≡ W - L ≡ R + W - R - L  mod 2C
         --             ≡ R + N - L      mod 2C  (by Lemma_Mod_Add_Simp)
         --             ≡ R + dR         mod 2C
         pragma Assert (N - dR <= C);
         Lemma_Mod_Add_Simp (R - L, W - R, 2*C);
         pragma Assert (Rp = (R + dR) mod (2*C));
         Lemma_Pop_Decreases_Length (R, W, C, N, Np, dR);
         pragma Assert (Np = L);
         pragma Assert (Length (NewB) = Natural'Min (To_Length, OldN));

         --  Proof that the new buffer is valid:
         pragma Assert (Is_Valid (NewB));
         B := NewB;

         --  Proof that truncate leaves back elements unchanged:
         for I in 0 .. Length (B) - 1 loop
            Lemma_Pop_Shifts_Back_Elements (R, Rp, C, To_Big_Integer (I), N - Np);
            pragma Assert (Mask (B, OldB.Read + (I + (Length (OldB) - Length (B)))) = Mask (B, B.Read + I));
            pragma Assert (Get (OldB, I + (Length (OldB) - Length (B))) = Get (B, I));
            pragma Loop_Invariant (for all K in 0 .. I => Get (OldB, K + (Length (OldB) - Length (B))) = Get (B, K));
         end loop;
      end if;
   end Truncate_Back;

end Ring_Buffer;
