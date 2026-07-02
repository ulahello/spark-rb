pragma Ada_2022;

with Spark_Rb;

package Integer_Test
  with SPARK_Mode => On
is

   --  Ring buffer is generic to element type, I'm instantiating it on integers
   --  just to have something to work with when writing proofs.
   package Rb_Integer is new Spark_Rb (Element => Integer, Uninit => 0);

end Integer_Test;
