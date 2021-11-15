#[macro_use]
mod run_test;

output_test!(test_print_i64, "print(2)", "2\n");
output_test!(test_print_f64, "print(42.13)", "42.13\n");

output_test!(test_multiply, "print(3.2 * 2.4)", "7.68\n");

output_test!(test_define_type, "type X = { x }", "");

output_test!(
    test_empty_constructor,
    r#"
      type X = {}
      {
        X()
        # suppress output
        void
      }
    "#,
    ""
);
output_test!(
    test_constructor_with_arguments,
    r#"
      type X = { x, y: i64 }
      {
        X(2.13, 3)
        # suppress output
        void
      }
    "#,
    ""
);
output_test!(
    test_accessors,
    r#"
      type X = { x, y: i64 }
      X(2.13, 3).x.print()
      X(2.13, 3).y.print()
    "#,
    "2.13\n3\n"
);

output_test!(
    test_custom_print,
    r#"
      type X = { blah }
      fn print(x: X) = print(x.blah)
      print(X(42))
    "#,
    "42\n"
);
