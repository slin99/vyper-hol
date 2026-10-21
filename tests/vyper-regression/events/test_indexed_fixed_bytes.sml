val () = List.app (fn traces =>
  let
    val result = mk_comb (``regression_first_log_topics``,
      mk_comb (``run_regression_traces``, traces))
    val expected = ``SOME
      [0xc24508c989449ac13ef418e13692063a60e4b70a2ff8591d4421ae9064d5d0c1;
       0x1111111111111111111111111111111111111111000000000000000000000000]``
    val th = cv_eval (mk_eq (result, expected))
    val _ = EQT_ELIM th handle HOL_ERR _ =>
      raise Fail "indexed bytes20 event topic is not right-padded"
  in () end) regression_traces;
