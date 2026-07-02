[doc('Run gnatprove to verify the package against its specification.')]
prove:
	gnatprove -P spark_rb.gpr --pedantic --prover=z3

[doc('Format the code with gnatformat.')]
fmt:
	gnatformat -P spark_rb.gpr --charset utf8
