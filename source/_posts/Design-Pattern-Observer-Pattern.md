---
title: Design Pattern - Observer Pattern
top: false
cover: false
toc: true
mathjax: true
date: 2020-05-06 18:22:24
password:
summary:
tags: Design Pattern
categories: pattern
---

# Observer Pattern
<!--- more --->
observer pattern本质上就是一个广播机制。很多的编程语言或库文件中都有集成好的实现。

例子，
~~~verilog
typedef Subscriber;

class Broadcaster;
  Subscriber subscribers[string];
  
  function new();
  endfunction
  
  function void register(string name, Subscriber s);
    this.subscribers[name] = s;
  endfunction
  
  function void unregister(string name);
    this.subscribers.delete(name);
  endfunction
  
  function void broadcast();
    foreach(this.subscribers[s]) begin
	  string tmps = s;
	  fork
	    this.subscribers[tmps].notify_action(...pass useful data...);
	  join_none
	end
	wait fork;
  endfunction
endclass

class Subscriber;
  Broadcaster broadcaster;
  
  function new(Broadcaster broadcaster);
    this.broadcaster = broadcaster;
  endfunction
  
  function void notify_action(somedata d);
    ...
	// maybe access broadcaster for some reason
	this.broadcaster....
	...
  endfunction
endclass

Broadcaster broadcaster = new();
Subscriber subscriber = new(broadcaster);
broadcaster.register("first_subscriber", subscriber);
broadcaster.broadcast();
broadcaster.unregister("first_subscriber");
~~~

例子里的broadcast()用了多线程，因为原则上广播机制应该是对所有的接受者并发进行广播。但如果没有严格意义的时间概念或者竞争问题，就不用太在意这个。
接收者的构造函数里还包含了广播者本身，这其实可以看做是一个observer pattern的扩展，最简单的observer pattern并没有这一点。它的加入是为了有的时候接收者可能会要访问广播者提供可能。

在UVM的机制里，observer pattern已经由analysis port和uvm_subscriber实现。

