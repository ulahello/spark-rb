pragma Ada_2022;

--  TODO: run gnatformat (trying and failing to get it to compile)

with Ring_Buffer;

package Spark_Rb
  with SPARK_Mode => On
is

   --  HACK: Ring buffer is generic to element type, I'm instantiating
   --  it on integers just to have something to work with when writing
   --  proofs.
   package Rb_Integer is
      new Ring_Buffer (Element => Integer,
                       Uninit => 0);

end Spark_Rb;
