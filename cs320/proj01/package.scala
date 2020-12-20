package cs320

package object proj01 extends Project01 {

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

  def M(f:(Expr, Env) => Value, env:Env, x:List[String], v:List[Expr]): Env = x match {  
      case h::t => M(f, env, t, v.tail) + (h -> f(v.head, env)) 
      case Nil => Map() 
  }
  def mapping(g:(Expr, Env) => Value, env:Env, x:List[String], v:List[Expr]): Env = {
    if( x.size == v.size ) {M(g, env, x, v)} 
    else {error("wrong arity")}
  }
  

  def Recfun(ds: List[FunDef], env:Env):Env = ds match{
    case h::t => { 
      val cloV = CloV(h.ps, h.b, env) 
      val nenv = env + (h.n -> cloV)
      val fnenv = Recfun(t, nenv)
      cloV.env = fnenv
      fnenv
      }
    case Nil => env
  }

  def interp(e: Expr, env: Env): Value = e match{
    case IntE(n) => IntV(n)
    case Add(l, r) => Op(_ + _)(interp(l, env), interp(r, env))
    case Mul(l, r) => Op(_ * _)(interp(l, env), interp(r, env))
    case Div(l, r) => interp(r, env) match {
      case IntV(0) => error("devide by zero!")
      case x @ _ => Op(_ / _)(interp(l, env), x)
    }
    case Mod(l, r) => interp(r, env) match {
      case IntV(0) => error("devide by zero!")
      case x @ _ => Op(_ % _)(interp(l, env), x)
    }
    case BooleanE(b) => BooleanV(b)
    case Eq(l, r) => Bop(_ == _)(interp(l, env), interp(r, env))
    case Lt(l, r) => Bop(_ < _)(interp(l, env), interp(r, env))
    case TupleE(es) => TupleV(es.map(interp(_, env)))
    case Proj(t, i) => interp(t, env) match {
        case TupleV(vs) => {
          if( i <= vs.size && 0 < i ) {vs(i-1)}
          else {error(s"wrong index: $i")} 
            }
        case _ => error("Not a TupleV")
          }
    case NilE => NilV
    case ConsE(h, t) => interp(t, env) match {
      case c@(ConsV(_, _) | NilV) => ConsV(interp(h, env), c) 
      case _ => error("not a list")
      }
    case Empty(l) => interp(l, env) match {
      case NilV => BooleanV(true)
      case ConsV(_,_) => BooleanV(false)
      case _ => error("Not a list!")
    }
    case Head(l) => interp(l, env) match {
      case ConsV(h, t) => h 
      case _ => error("not a list!")
      }
    case Tail(l) => interp(l, env) match {
      case ConsV(h, t) => t 
      case _ => error("not a list!")
      }
    case Id(x) => env.getOrElse(x, error(s"free identifier: $x"))
    case Val(x, e, b) => interp(b, env + (x -> interp(e, env)))
    case Fun(ps, b) => CloV(ps, b, env)
    case App(f, as) => interp(f, env) match {
      case CloV(ps, b, fenv) => interp(b, fenv ++ mapping(interp, env, ps, as))
      case v => error(s"not a closure: $v")
    }
    case Test(e, t) => interp(e, env) match {
      case IntV(n) => BooleanV(IntT == t)
      case BooleanV(b) => BooleanV(BooleanT == t)
      case TupleV(vs) => BooleanV(TupleT == t)
      case NilV => BooleanV(ListT == t)
      case ConsV(h, tail) => BooleanV(ListT == t)
      case CloV(ps, b, env) => BooleanV(FunctionT == t)
    }
    case If(c, t, f) => interp(c, env) match {
      case BooleanV(true) => interp(t, env)
      case BooleanV(false) => interp(f, env)
      case _ => error("c is not a BooleanV")
    }
    case RecFuns(ds, e) => interp(e, Recfun(ds, env))
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
    testExc(run("Nil.tail"), "need your own error message")
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
    testExc(run("5 / 0"), "error")
    // test-mod
    testExc(run("13 % 0"), "error")
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
    
    // test-local1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-local2
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
  }

}