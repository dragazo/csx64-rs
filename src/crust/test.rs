use super::ast::grammar::ProgramParser;
use super::ast::*;

#[test]
fn test_crust() {
    let res = ProgramParser::new().parse(r#"
void foo() {
    usize val = 12.5 + 5 * 2 - 5;
}
    "#).unwrap();
    assert_eq!(res.len(), 1);
    let foo = match &res[0] {
        Item::Function(x) => x,
        x => panic!("{:?}", x),
    };
    assert!(matches!(foo.ret, Type::Void));
    assert_eq!(foo.name.id, "foo");
    assert_eq!(foo.params.len(), 0);
    assert_eq!(foo.body.len(), 1);
    match &foo.body[0] {
        Stmt::VarDecl { ty, name, value } => {
            assert!(matches!(ty, Type::Integer(IntType::Usize)));
            assert_eq!(name.id, "val");
            match value {
                Expr::Sub { left, right } => {
                    match &**left {
                        Expr::Add { left, right } => {
                            match &**left {
                                Expr::Value(Value::Float(v)) => assert_eq!(v.value, 12.5),
                                x => panic!("{:?}", x),
                            }
                            match &**right {
                                Expr::Mul { .. } => (),
                                x => panic!("{:?}", x),
                            }
                        }
                        x => panic!("{:?}", x),
                    }
                    match &**right {
                        Expr::Value(Value::Integer(v)) => assert_eq!(v.value, 5),
                        x => panic!("{:?}", x),
                    }
                }
                x => panic!("{:?}", x),
            }
        }
        x => panic!("{:?}", x),
    }
}
