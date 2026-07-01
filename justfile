[doc('Run gnatprove to verify the package against its specification.')]
prove:
	gnatprove -P spark_rb.gpr --pedantic --prover=z3
