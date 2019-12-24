---
title: factory in UVM
top: false
cover: false
toc: true
mathjax: true
date: 2019-12-24 18:43:45
password:
summary:
tags: UVM
categories: SystemVerilog
---


UVM的工厂机制是实现复用性的关键，这次稍微展开看一下它的实现过程。
<!--- more --->

# 1. factory
uvm_factory这个类是一个纯虚类。在其内部只有两个静态函数，其余的都是要被子类覆写的纯虚函数。所以这里简单地看一下这两个纯虚函数就跳到它的实现类uvm_default_factory继续察看其他内容。
~~~
static function uvm_factory get();
	uvm_coreservice_t s;
	s = uvm_coreservice_t::get();
	return s.get_factory();
endfunction	

static function void set(uvm_factory f);
	uvm_coreservice_t s;
	s = uvm_coreservice_t::get();
	s.set_factory(f);
endfunction
~~~
这两个函数一个是得到factory的实例对象，另一个是用于更改系统中默认的factory实例对象。它们都用到了一个共同的类uvm_coreservice_t，这里类可以暂时简单地看成是一个全局 变量/组件 的 设定/提供 器。对于一些全局性的组件，比如uvm_factory，uvm_report_server，uvm_printer等等，uvm_coreservice_t提供的API可以直接获取它们的实例对象或对已有的实例对象进行替换更改。


# 2. default_factory
这个类实现了factory中核心的注册和覆写机制。其本质是利用hashmap(在sv中叫associative array)来进行类名，实例对象等的存储，在用时根据目的进行读取。
它声明了如下的存储变量:
~~~
protected bit                     m_types[uvm_object_wrapper];
protected bit                     m_lookup_strs[string]; // TODO
protected uvm_object_wrapper      m_type_names[string];
protected m_inst_typename_alias_t m_inst_aliases[$];     // TODO
protected uvm_factory_override    m_type_overrides[$];
protected uvm_factory_override    m_inst_overrides[$];
local uvm_factory_override        m_override_info[$];    // TODO
~~~
m_types里存放“uvm_object_wrapper-是否存在”的键值对。可根据uvm_object_wrapper察看其是否被注册。
m_type_names里存放“类名-uvm_object_wrapper”的键值对。可根据类名获得相应的实例对象。
m_type_overrides里存放通过set_type_override()进行覆写的信息，如原始类型、目的类型等。
m_inst_overrides里存放通过set_inst_override()进行覆写的信息，如原始类型、目的类型等。


下面是类成元函数:
~~~
virtual function void register (uvm_object_wrapper obj);
virtual function void set_inst_override_by_type (uvm_object_wrapper original_type, uvm_object_wrapper override_type, string full_inst_path);
virtual function void set_inst_override_by_name (string original_type_name, string override_type_name, string full_inst_path);
virtual function void set_type_override_by_type (uvm_object_wrapper original_type, uvm_object_wrapper override_type, bit replace=1);
virtual function void set_type_override_by_name (string original_type_name, string override_type_name, bit replace=1);
virtual function void set_type_alias(string alias_type_name, uvm_object_wrapper original_type); 
virtual function void set_inst_alias(string alias_type_name, uvm_object_wrapper original_type, string full_inst_path);
virtual function uvm_object create_object_by_type(uvm_object_wrapper requested_type, string parent_inst_path="", string name="");
virtual function uvm_component create_component_by_type (uvm_object_wrapper requested_type, string parent_inst_path="", string name, uvm_component parent);
virtual function uvm_object create_object_by_name(string requested_type_name, string parent_inst_path="", string name=""); 
virtual function uvm_component create_component_by_name (string requested_type_name, string parent_inst_path="", string name, uvm_component parent);
virtual function bit is_type_name_registered(string type_name);
virtual function bit is_type_registered(uvm_object_wrapper obj);
virtual function uvm_object_wrapper find_wrapper_by_name(string type_name); // TODO
virtual function uvm_object_wrapper find_override_by_type (uvm_object_wrapper requested_type, string full_inst_path);  // TODO
virtual function uvm_object_wrapper find_override_by_name (string requested_type_name, string full_inst_path);  // TODO
virtual function void print (int all_types=1); // Prints the state of the uvm_factory, including registered types, instance overrides, and type overrides.

// Only for debug use, same as create_*_by_* methods above but it shall generate more 
// detailing message describing how the object or components have constructed or overrided.
virtual function void debug_create_by_type (uvm_object_wrapper requested_type, string parent_inst_path="", string name="");
virtual function void debug_create_by_name (string requested_type_name, string parent_inst_path="", string name="");
protected function void m_debug_create(string requested_type_name, uvm_object_wrapper requested_type, string parent_inst_path, string name);
protected function void m_debug_display(string requested_type_name, uvm_object_wrapper result, string full_inst_path);

function uvm_object_wrapper m_resolve_type_name(string requested_type_name);
function uvm_object_wrapper m_resolve_type_name_by_inst(string requested_type_name, string full_inst_path);
function bit m_matches_type_pair(m_uvm_factory_type_pair_t match_type_pair, uvm_object_wrapper requested_type, string requested_type_name);
function bit m_matches_type_override(uvm_factory_override override, uvm_object_wrapper requested_type, string requested_type_name, string full_inst_path="", bit match_original_type=1, bit resolve_null_type_by_inst=0);
function bit m_matches_inst_override(uvm_factory_override override, uvm_object_wrapper requested_type, string requested_type_name, string full_inst_path="");
~~~
这么些个函数属实是有点小多，不过大多数可以通过名字和形参看出用途，所以定义函数名和形参名有时也是个技术活。中间的一些函数是调试使用的，会显示更多的调试信息，一般不使用。最后的一些函数是用于检查factory override时的匹配性。

# register
这个函数主要做两个事。一是通过obj的类名在m_types里创建键值对。二是将m_type_overrides和m_inst_overrides中关于原始类型和目的类型信息都初始化为obj类型。

## set\_\*\_override\_by\_*
对于覆写的函数主要有两方面，一方面覆写方式，另一方面是查找方式。

<table>
  <tbody>
  <tr>
    <th bgcolor=#f7f7f7><font color="Black">覆写方式/查找方式</font></th>
	<th bgcolor=#f7f7f7><font color="Black">通过类型名字查找</font></th>
	<th bgcolor=#f7f7f7><font color="Black">通过类型查找</font></th>
  </tr>
  <tr>
    <td bgcolor=#f7f7f7><font color="Black"><b>覆写整个类型</font></b></td>
	<td bgcolor=#f7f7f7><font color="Black">set_type_override_by_name</font></td>
	<td bgcolor=#f7f7f7><font color="Black">set_type_override_by_type</font></td> 
  </tr>
  <tr>
    <td bgcolor=#f7f7f7><font color="Black"><b>覆写具体路径实例</font></b></td>
	<td bgcolor=#f7f7f7><font color="Black">set_inst_override_by_name</font></td>
	<td bgcolor=#f7f7f7><font color="Black">set_inst_override_by_typee</font></td>
  </tr>
</table>

回想上面提到的两个队列m_type_overrides和m_inst_overrides，这两个队列分别对应着两种覆写方式的覆写信息，这些信息最终会在得到实例对象时使用。

*\_by\_name会从m_type_names中查找类型， *\_by\_type会从m_types中查找类型。
举例来说，set_inst_override_by_name(.original_type_name("typeA"), .override_type_name("typeB"), .full_inst_path("instA_path"))，函数内部会先对"typeA"，"typeB"做一系列hashmap的存在性检查，接着从m_type_names里取出相应的类型，然后在m_inst_overrides中记录:实例路径"instA_path"，原始类型及类型名，目标类型及类型名等信息。

## set\_\*\_alias
set_type_alias和set_inst_alias就是给相应的类型起一个别名。set_inst_alias会多要求一个实例的路径。

## create\_\*\_by\_*
这些函数会先构建一个"parent_inst_path.name"的路径名，然后通过之前记录的m_type_overrides和m_inst_overrides信息来建立实例对象。通过实例路径覆写的有优先性。

## is\_type\_\*\_registered
这些函数只是调用m_type_names.exists(type_name)，m_types.exists(type)来检查键值对是否存在。

