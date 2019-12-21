---
title: what's in uvm_object_utils_begin/end
top: false
cover: false
toc: true
mathjax: true
date: 2019-12-21 15:54:27
password:
summary:
tags: UVM
categories: SystemVerilog
---


uvm_object_utils_begin/end是在UVM框架中定义uvm_object子类时，经常要到的宏定义。
<!---more--->
但这个宏定义内部到底包含了什么一般并不是很清晰。这里简要的展开这个宏定义，看看里面到底定义了什么。

# 1. 宏定义展开
在UVM的源码中，uvm_object_utils_begin和uvm_object_utils_end的定义如下:

~~~
`define uvm_object_utils_begin(T) \
  `uvm_object_utils(T) \
  `uvm_field_utils_begin(T)
  
`define uvm_object_utils_end \
  `uvm_field_utils_end
~~~

进一步展开

~~~
`define uvm_object_utils(T) \
  `m_uvm_object_registry_internal(T,T)  \
  `m_uvm_object_create_func(T) \
  `uvm_type_name_decl(`"T`")

`define uvm_field_utils_end \
endfunction
~~~

也就是说，最终有如下的定义展开情况
~~~
`define uvm_object_utils_begin(T)
=========================================
  `m_uvm_object_registry_internal(T,T)
  `m_uvm_object_create_func(T)
  `uvm_type_name_decl(`"T`")
  `uvm_field_utils_begin(T)

`define uvm_object_utils_end
=========================================
endfunction
~~~

从宏定义的展开可以看出，uvm_object_utils_end很简单，只是一个endfunction。但这也给了我们一个简单的提示，宏uvm_object_utils_begin的内容肯定是函数定义有关的，所以才会用endfunction作为结尾。

uvm_object_utils_begin包含了其他几个宏，这里先不考虑最后一个宏uvm_field_utils_begin，这个宏从名字上就可以看出是和自定义的类成员变量的filed automation有关，即那些uvm_field_int, uvm_field_string等等。剩下的我们一个个来看。


# 2. uvm_object_utils_begin展开
- uvm_type_name_decl
~~~
`define uvm_type_name_decl(TNAME_STRING)
==========================================
static function string type_name();
  return TNAME_STRING;
endfunction : type_name
     
virtual function string get_type_name();
  return TNAME_STRING;
endfunction : get_type_name
~~~
uvm_type_name_decl较为简单，只是定义了两个函数用于返回TNAME_STRING，而TNAME_STRING就是uvm_object_utils_begin(T)中的T的字符串形式。

- m_uvm_object_registry_internal
~~~
`define m_uvm_object_registry_internal(T,S)
==================================================
typedef uvm_object_registry#(T,`"S`") type_id;

static function type_id get_type();
  return type_id::get();
endfunction

virtual function uvm_object_wrapper get_object_type();
  return type_id::get();
endfunction
~~~
m_uvm_object_registry_internal定义了一个类型type_id，这个type_id是uvm_object_registry#(T,"S")类型。同时定义了两个函数来调用uvm_object_registry#(T,"S")::get()。如果想深入找下去可以发现这个get()函数本质上是返回来一个uvm_object_registry#(T,"S")的实例对象。也就是说，get_type()和get_object_type()其实得到了一个uvm_object_registry#(T,"S")的实例对象。而get_object_type()在返回时又添了一层对uvm_object_wrapper的多态。这里的T和S就是uvm_object_utils_begin(T)中的T和T的字符串形式。


- m_uvm_object_create_func
~~~
`define m_uvm_object_create_func(T)
======================================
function uvm_object create (string name="");
  T tmp;
  tmp = new();
  if (name!="") tmp.set_name(name);
  return tmp;
endfunction
======================================
~~~
m_uvm_object_create_func定义了一个create()函数，这个函数返回一个T类型的实例对象，并在返回时做了对uvm_object的多态。回想创建一般实例对象的时候，我们是用class_name::type_id::create("name")的形式来让被创建的实例可以在uvm_factory中进行注册，而不是class_name::create("name")。所以这里m_uvm_object_create_func定义的create()函数并不会被直接使用，使用的其实是type_id，即uvm_object_registry#(T,"S")的create()函数。
若进一步察看，uvm_object_registry#(T,"S")的create()函数是经过多层覆写来实现的，包含了底层的uvm_fatory实例注册机制。所以真正的注册过程其实是在class_name::type_id::create("name")这一步上。

# 3. 小结
宏uvm_object_utils_begin(T)本质上其实是定义了一些函数，变量和类型。其中最关键的是type_id这个类型。因为我们在UVM框架中创建实例的时候一般是用class_name::type_id::create("name")的形式来让被创建的实例可以在uvm_factory中进行注册，而这里的type_id就是在宏uvm_object_utils_begin(T)中定义的。type_id，即uvm_object_registry#(T,"S")中的create()函数实现了底层的uvm_fatory实例注册过程。
