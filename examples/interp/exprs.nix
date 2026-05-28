# Scalable expression generators for benchmarking.
{ num, var, add, mul, sub, lt, eq, if_, let_, lam, app, ... }:

let
  # let fib = λn. if n < 2 then n else fib(n-1) + fib(n-2) in fib(N)
  mkFib = n:
    let_ "fib"
      (lam "n"
        (if_ (lt (var "n") (num 2))
          (var "n")
          (add
            (app (var "fib") (sub (var "n") (num 1)))
            (app (var "fib") (sub (var "n") (num 2))))))
      (app (var "fib") (num n));

  # let x0 = 0 in let x1 = x0+1 in ... in xN
  mkNestedLets = n:
    let
      go = i:
        if i >= n then var "x${toString (n - 1)}"
        else if i == 0 then let_ "x0" (num 0) (go 1)
        else let_ "x${toString i}" (add (var "x${toString (i - 1)}") (num 1)) (go (i + 1));
    in
    go 0;

  # let sum = λn. if n == 0 then 0 else n + sum(n-1) in sum(N)
  mkSum = n:
    let_ "sum"
      (lam "n"
        (if_ (eq (var "n") (num 0))
          (num 0)
          (add (var "n") (app (var "sum") (sub (var "n") (num 1))))))
      (app (var "sum") (num n));

  # Ackermann: grows extremely fast
  mkAck = m: n:
    let_ "ack"
      (lam "m" (lam "n"
        (if_ (eq (var "m") (num 0))
          (add (var "n") (num 1))
          (if_ (eq (var "n") (num 0))
            (app (app (var "ack") (sub (var "m") (num 1))) (num 1))
            (app (app (var "ack") (sub (var "m") (num 1)))
              (app (app (var "ack") (var "m")) (sub (var "n") (num 1))))))))
      (app (app (var "ack") (num m)) (num n));

  mkFact = n:
    let_ "fact"
      (lam "n"
        (if_ (eq (var "n") (num 0))
          (num 1)
          (mul (var "n") (app (var "fact") (sub (var "n") (num 1))))))
      (app (var "fact") (num n));

  mkCountdown = n:
    let_ "countdown"
      (lam "n"
        (if_ (eq (var "n") (num 0))
          (num 0)
          (app (var "countdown") (sub (var "n") (num 1)))))
      (app (var "countdown") (num n));

in
{
  inherit mkFib mkNestedLets mkSum mkAck mkFact mkCountdown;

  benchmarks = {
    fib10 = mkFib 10;
    fib15 = mkFib 15;
    fib20 = mkFib 20;
    fib25 = mkFib 25;

    lets100 = mkNestedLets 100;
    lets500 = mkNestedLets 500;
    lets1000 = mkNestedLets 1000;
    lets5000 = mkNestedLets 5000;

    sum100 = mkSum 100;
    sum1000 = mkSum 1000;
    sum5000 = mkSum 5000;
    sum10000 = mkSum 10000;

    fact10 = mkFact 10;
    fact15 = mkFact 15;
    fact20 = mkFact 20;

    countdown1000 = mkCountdown 1000;
    countdown10000 = mkCountdown 10000;

    ack22 = mkAck 2 2;
    ack23 = mkAck 2 3;
    ack30 = mkAck 3 0;
    ack31 = mkAck 3 1;
    ack32 = mkAck 3 2;
    ack33 = mkAck 3 3;
    ack34 = mkAck 3 4;
  };
}
