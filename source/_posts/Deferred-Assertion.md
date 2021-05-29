---
title: Deferred Assertion
top: false
cover: false
toc: true
mathjax: true
date: 2020-06-05 20:49:33
password:
summary:
tags: SVA
categories: SystemVerilog
---

Deferred Assertion字面意义上值被延后的断言。它的用处是避免assertion在同一时间片内出现检测竞争。
<!--- more --->

# 1. what is deferred assertion ?
Deferred Assertion在最初的LRM中是没有这个概念的，直到后来09版被加入。

为了更好的理解，考虑下面一段代码
~~~verilog
logic a, b;

assign b = ~a;

always_comb begin
  assert(b !== a);
end
~~~

这段代码很简单，就是一个immediate assertion。通过逻辑分析，assert(b !== a)这个断言应该一直成立。但实际上，在仿真过程中此断言有可能会失败。
原因是assign语句的赋值和assert在同一时间片内有竞争。在当前时间片要更新的瞬间，有可能a更新了, 但b还没有更新，此时出现了a和b一瞬间的相同，而恰好的assert进行了检测造成失败。

这种现象和SV本身的时间机制有关。SV的一个时间片可以分为Preponed，Pre-active，Active，...，observed，...，Posponed等等区域，SV的不同语句会在不同区域被执行。而这里就是因为assign和assert的默认执行顺序错误。

要解决上面的问题，最好的方法就是把assert放在所有信号都变化完毕的posponed区域再执行。Deferred Assertion就是做这个事的。

Deferred Assertion的形式是在assert后加一个"final"或"#0":
1. Observed deferred assertion: assert ***#0***    (b !== a) [action block];
2. Final deferred assertion:    assert ***final*** (b !== a) [action block];

二者的区别在于:
Observed deferred assertion的[action block]分派在Re-active region，而Final deferred assertion的[action block]则是在postponed region.
Final deferred assertion更加稳定。因为一个时间片中的Observed region有可能被多次执行。
比如在program里更改了module中的某个信号值，从而导致observed region再次执行。这有可能导致Observed deferred assertion对glitch的误报。

Deferred Assertion的另外一个好处是可以脱离procedural block，即不用必须放在begin-end等等过程执行的语法块里面。
Immediate assertion是必须要放在procedural block里面的，否则会语法报错。

事实上，Deferred Assertion可以完全替代Immediate assertion，而且仿真更安全稳定。


# 2. Deferred assertion disabling
Deferred assertion是可以被取消的。
~~~verilog
always @(bad_val or bad_val_ok) begin : b1
  a1: assert #0 (bad_val) else $fatal(1, "Sorry"); 
  if (bad_val_ok) begin 
    disable a1;
  end 
end 
~~~


# 3. 小结
如果要用Immediate assertion的话，就用Deferred Assertion替代。
