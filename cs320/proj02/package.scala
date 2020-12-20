package cs320

package object proj02 extends Project02 {

  def Op(op:(Int, Int) => Int) : (Value, Value) => Value =
  (_, _) match{
    case (IntV(x), IntV(y)) => IntV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  } 

  def Bop(op:(Int, Int) => Boolean) : (Value, Value) => Value =
  (_, _) match{
    case (IntV(x), IntV(y)) => BooleanV(op(x, y))
    case (x, y) => error(s"not both integer: $x, $y")
  } 

  def Tp(es:List[Expr], vs:List[Value], f:(Expr, Env, Cont, ECont)=>Value, env: Env, k: Cont, ek: ECont):Value = es match {
      case h::t => interp(h, env, v => Tp(t, vs ::: List(v), f, env, k, ek), ek)
      case Nil => k(TupleV(vs))
  }

  def Ap(fv:Value, as:List[Expr], av:List[Value], f:(Expr, Env, Cont, ECont)=>Value, env: Env, k: Cont, ek: ECont):Value = as match {
      case h::t => interp(h, env, v => Ap(fv, t, av ::: List(v), f, env, k, ek), ek)
      case Nil => fv match {
        case CloV(ps, b, fenv) => if (av.length == ps.length){interp(b, fenv ++ (ps zip av), k, ek)
          } else{error("wrong arity")}
        case ContV(kv) => if(av.length == 1){kv(av.head)} else{error("wrong arity")}
        case v => error("not a closure: $v")
      }
  }


  def Recfun(ds: List[FunDef], env:Env):Env = ds match{
    case h::t => { 
      val cloV = CloV(h.parameters, h.body, env) 
      val nenv = env + (h.name -> cloV)
      val fnenv = Recfun(t, nenv)
      cloV.env = fnenv
      fnenv
      }
    case Nil => env
  }


  def interp(e: Expr, env: Env, k: Cont, ek: ECont): Value = e match {
    case Id(x) => k(env.getOrElse(x, error(s"free identifier: $x")))
    case IntE(n) => k(IntV(n))
    case BooleanE(b) => k(BooleanV(b))
    case Add(l, r) => interp(l, env, lv => interp(r, env, rv => k(Op(_+_)(lv, rv)), ek), ek) 
    case Mul(l, r) => interp(l, env, lv => interp(r, env, rv => k(Op(_*_)(lv, rv)), ek), ek) 
    case Div(l, r) => interp(l, env, lv => interp(r, env, rv => rv match {
      case IntV(0) => error("divide by zero")
      case _ => k(Op(_/_)(lv, rv)) }
      , ek), ek)
    case Mod(l, r) => interp(l, env, lv => interp(r, env, rv => rv match {
      case IntV(0) => error("divide by zero")
      case _ => k(Op(_%_)(lv, rv)) 
      }, ek), ek)
    case Eq(l, r) => interp(l, env, lv => interp(r, env, rv => k(Bop(_==_)(lv, rv)), ek), ek)
    case Lt(l, r) => interp(l, env, lv => interp(r, env, rv => k(Bop(_<_)(lv, rv)), ek), ek)
    case If(c,t,f) => interp(c, env, v => v match {
      case BooleanV(true) => interp(t, env, k, ek)
      case BooleanV(false) => interp(f, env, k, ek)
      case _ => error("condition is not a Boolean")
    }, ek)
    
    case TupleE(es) => Tp(es, List(), interp, env, k, ek)
    case Proj(t, i) => interp(t, env, v => v match {
        case TupleV(vs) => {
          if( i <= vs.size && 0 < i ) {k(vs(i-1))}
          else {error(s"wrong index: $i")} 
            }
        case _ => error("Not a TupleV")
          }, ek)
    
    case NilE => k(NilV)
    case ConsE(h, t) => interp(h, env, u => interp(t, env, v => v match{ 
      case ConsV(_, _) | NilV => k(ConsV(u, v)) 
      case _ => error("not a list")
      }, ek), ek)
    case Empty(l) => interp(l, env, v => v match { 
      case NilV => k(BooleanV(true))
      case ConsV(_,_) => k(BooleanV(false))
      case _ => error("not a list")
    }, ek)
    case Head(l) => interp(l, env, v => v match { 
      case NilV => error("empty list")
      case ConsV(h,_) => k(h)
      case _ => error("not a list")
    }, ek)
    case Tail(l) => interp(l, env, v => v match { 
      case NilV => error("empty list")
      case ConsV(_,t) => k(t)
      case _ => error("not a list")
    }, ek)
    case Val(x, e, b) => interp(e, env, v => interp(b, env + (x -> v), k, ek), ek) 
    case Vcc(x, e) => interp(e, env + (x -> ContV(k)), k, ek)
    case Fun(ps, b) => k(CloV(ps, b, env))
    case RecFuns(ds, e) => interp(e, Recfun(ds, env), k, ek)
    case App(f, as) => interp(f, env, fv => Ap(fv, as, List(), interp, env, k, ek), ek)
    case Test(e, t) => interp(e, env, v => v match {
      case IntV(_) => k(BooleanV(IntT == t))
      case BooleanV(b) => k(BooleanV(BooleanT == t))
      case TupleV(vs) => k(BooleanV(TupleT == t))
      case NilV => k(BooleanV(ListT == t))
      case ConsV(h, tail) => k(BooleanV(ListT == t))
      case CloV(ps, b, env) => k(BooleanV(FunctionT == t))
      case ContV(c) => k(BooleanV(FunctionT == t))
    }, ek)
    case Throw(e) => ek match {
      case None => error("An exception is thrown, but no handler is found")
      case Some(v) => interp(e, env, v, ek)
      }
    case Try(e, h) => interp(e, env, k, Some(v => interp(h, env, u => u match {
      case CloV(ps, b, env) => 
        if(ps.length == 1){interp(b, env + (ps.head -> v), k, ek)}
        else {error("not a single parameter for catching")}
      case ContV(c) => c(v)
      case _ =>  error("not a closure or continuation")
    }, ek)))
  }
 
  def test6: Unit = {
    test(run("(1, 2 + 3, true)._1"), "1")
    test(run("((42, 3 * 2), false)._1._2"), "6")
    test(run("val (x, y) = (3, 7); (x, y)"), "(3, 7)")
    testExc(run("try {1 :: (throw 4) :: (throw 2)} catch (v => v"), "4")
    testExc(run("try {1 :: throw 4 :: throw 2} catch (v => v"), "2")
    testExc(run("try { throw throw 2} catch (v => v"), "2")

    testExc(run("(1, 2 + 3, throw 2)._1"), "")
    test(run("""
      try {(1, 2 + 3, throw 2)._1}
      catch (x => x)
    """), "2")
    test(run("""
      try {2}
      catch x
    """), "2")
    testExc(run("""
      try {
        throw 2
      } catch (
        x
      )
    """), "")
    test(run("""
      try {
        throw 2
      } catch (
        x => x
      )
    """), "2")
    test(run("(x => return 1)(x => x).isInstanceOf[Int]"), "true")
    testExc(run("(x => return 1)(x).isInstanceOf[Tuple]"), "free id")
    testExc(run("(x => throw 2)(3).isInstanceOf[Int]"), "handler")
    test(run("""
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      def g(x) = f(x) + h(x);
      def h(x) = if (x < 1) return 1 else x * h(x - 1);
      g(5)
    """), "135")
    test(run("""
      vcc x;
      1 
      + x( (x => return 1)(3) ) 
      + 1
    """), "1")
    test(run("""
      def div(x) = (x => 10 / x)(
        if (x == 0) return 0 else x
      );
      div(0)
    """), "0")
    // test-try2
    test(run("""
      1 + vcc x;
        try {
          throw 1
        } catch x
    """), "2")
    // test-vcc2
    test(run("""
      (x => x * x)(
        1 + vcc x; 1 + x(2) + 3
      )
    """), "9")
  }


  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-add
    test(run("1 + 2"), "3")
    // test-sub
    test(run("7 - 2"), "5")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-neg
    test(run("1 - -1"), "2")

    // test-boolean
    test(run("true"), "true")
    // test-eq
    test(run("1 == 3 - 2"), "true")
    // test-lt
    test(run("1 < 3 - 2"), "false")

    // test-tuple1
    test(run("(1, 2 + 3, true)"), "(1, 5, true)")
    // test-tuple2
    test(run("((42, 3 * 2), false)"), "((42, 6), false)")
    // test-proj1
    test(run("(1, 2 + 3, true)._1"), "1")
    // test-proj2
    test(run("((42, 3 * 2), false)._1._2"), "6")

    // test-nil
    test(run("Nil"), "Nil")
    // test-cons
    test(run("1 :: 1 + 1 :: Nil"), "(1 :: (2 :: Nil))")
    // test-isempty1
    test(run("Nil.isEmpty"), "true")
    // test-isempty2
    test(run("(1 :: Nil).isEmpty"), "false")
    // test-head
    test(run("(1 :: Nil).head"), "1")
    // test-tail
    test(run("(1 :: Nil).tail"), "Nil")
    // test-tail-head
    test(run("(1 :: 2 :: Nil).tail.head"), "2")

    // test-val1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-val2
    test(run("""
      val (x, y) = (1 + 2, 3 + 4);
      val z = x * y;
      val (a, b, c) = (z, z + z, z + z + z);
      c - b
    """), "21")

    // test-fun
    test(run("x => x + x"), "<function>")
    // test-app1
    test(run("(x => x + x)(1)"), "2")
    // test-app2
    test(run("(x => y => x + y)(1)(2)"), "3")
    // test-app3
    test(run("((x, y) => x + y)(1, 2)"), "3")

    // test-type1
    test(run("1.isInstanceOf[Int]"), "true")
    // test-type2
    test(run("1.isInstanceOf[Boolean]"), "false")
    // test-type3
    test(run("(1 :: Nil).isInstanceOf[List]"), "true")
    // test-type4
    test(run("(x => x + x).isInstanceOf[Function]"), "true")

    // test-if
    test(run("if (true) 1 else 2"), "1")
    // test-not
    test(run("!true"), "false")
    // test-and
    test(run("true && false"), "false")
    // test-or
    test(run("true || false"), "true")
    // test-neq
    test(run("1 != 2"), "true")
    // test-lte
    test(run("1 <= 1"), "true")
    // test-gt
    test(run("1 > 1"), "false")
    // test-gte
    test(run("1 >= 1"), "true")
    // test-nonempty
    test(run("Nil.nonEmpty"), "false")

    // test-rec1
    test(run("""
      def f(x) = x - 1;
      f(2)
    """), "1")
    // test-rec2
    test(run("""
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")

    // test-vcc1
    test(run("""
      vcc x;
      1 + x(1) + 1
    """), "1")
    // test-vcc2
    test(run("""
      (x => x * x)(
        1 + vcc x; 1 + x(2) + 3
      )
    """), "9")

    // test-return1
    test(run("(x => (return 1) + x)(2)"), "1")
    // test-return2
    test(run("""
      def div(x) = (x => 10 / x)(
        if (x == 0) return 0 else x
      );
      div(0) + div(10)
    """), "1")

    // test-throw1
    testExc(run("throw 1"), "")
    // test-throw2
    testExc(run("throw throw 1"), "")

    // test-try1
    test(run("""
      try {
        throw 1
      } catch (
        x => x + x
      )
    """), "2")
    // test-try2
    test(run("""
      1 + vcc x;
        try {
          throw 1
        } catch x
    """), "2")
  }
    def test1: Unit = {
    // test-type1
    test(run("1.isInstanceOf[Int]"), "true")
    // test-type2
    test(run("1.isInstanceOf[Boolean]"), "false")
    // test-type3
    test(run("(1 :: Nil).isInstanceOf[List]"), "true")
    // test-type4
    test(run("(x => x + x).isInstanceOf[Function]"), "true")
    //
    test(run("(x => x + x).isInstanceOf[List]"), "false")
    //test tail when the list is empty
    testExc(run("Nil.tail"), "empty list")
    //test tuple when length < 2
    test(run("(1)"), "1")
    //type
    test(run("(1).isInstanceOf[Tuple]"), "false")
    //rec
    test(run("""
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      def g(x) = f(x) + h(x);
      def h(x) = if (x < 1) 1 else x * h(x - 1);
      g(5)
    """), "135")
  }

  def test2: Unit = {
    // test-int
    test(run("- 42"), "-42")
    // test-sub
    test(run("- 7 + 2"), "-5")
    // test-div
    testExc(run("5 / 0"), "divide by zero")
    // test-mod
    testExc(run("13 % 0"), "divide by zero")
    // test-proj2
    test(run("(((42, 3 * 2), 7-5), false)._1._1._2"), "6")
    test(run("((((42,(1 :: (1+1 :: Nil), 7)), 3 * 2), 7-5), false)._1._1._1._2._1"), "(1 :: (2 :: Nil))")
    
    // test-tail-head
    testExc(run("(1 :: 2 :: Nil).tail.head.head"), "")
    test(run("((1 :: 2 :: Nil) :: (3 :: Nil) :: 4 :: Nil).head"), "(1 :: (2 :: Nil))")
    test(run("((1 :: 2 :: Nil) :: (3 :: Nil) :: 4 :: Nil).tail.head"), "(3 :: Nil)")
    test(run("((1 :: 2 :: Nil) :: (3 :: Nil) :: 4 :: Nil).head.tail.head"), "2")
    test(run("((1 :: 2 :: Nil) :: (3 :: Nil) :: 4 :: Nil).tail.head.head"), "3")
    test(run("((1 :: 2 :: Nil) :: (3 :: Nil) :: 4 :: Nil).tail.tail.head"), "4")
    test(run("(((x => x + x) :: Nil).head)(1)"), "2")
    test(run("(((((x => x + x) :: Nil), 3)._1).head)(1)"), "2")

    // test-app2
    test(run("(x => y => x - y)(1)(2)"), "-1")
    test(run("(x => y => x - y)(2)(1)"), "1")
  }

  def test3: Unit = {
    test(run("5"), "5")
    test(run("(5 + 5)"), "10")
    test(run("{ val x = (5 + 5); (x + x) }"), "20")
    test(run("{ val x = 5; (x + x) }"), "10")
    test(run("{ val x = (5 + 5); { val y = (x - 3); (y + y) } }"), "14")
    test(run("{ val x = 5; { val y = (x - 3); (y + y) } }"), "4")
    test(run("{ val x = 5; (x + { val x = 3; 10 }) }"), "15")
    test(run("{ val x = 5; (x + { val x = 3; x }) }"), "8")
    test(run("{ val x = 5; (x + { val y = 3; x }) }"), "10")
    test(run("{ val x = 5; { val y = x; y } }"), "5")
    test(run("{ val x = 5; { val x = x; x } }"), "5")
    test(run("{ val x = 2; ((x + x) - x) }"), "2")
  }

  def test5: Unit = {
    test(run("{ val f = { (a, b) => (a + b) }; { val g = { x => (x - 5) }; { val x = f(2, 5); g(x) } } }"), "2")
    test(run("{ val f = { (x, y) => (x + y) }; f(1, 2) }"), "3")
    test(run("{ val f = { () => 5 }; (f() + f()) }"), "10")
    test(run("{ val h = { (x, y, z, w) => (x + w) }; h(1, 4, 5, 6) }"), "7")
    test(run("{ val f = { () => 4 }; { val g = { x => (x + x) }; { val x = 10; ((x + f()) - g(4)) } } }"), "6")
  }
}