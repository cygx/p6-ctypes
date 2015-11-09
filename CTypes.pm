use v6;
use nqp;

my constant NativeHOW = int.HOW.WHAT; # HACK
my constant CHAR_BIT = 8;

my class Callsite is repr<NativeCall> {}
my class Void is repr<Uninstantiable> {}
my class ScalarRef { ... }
my class VMPtr is repr<CPointer> {
    method new(Int() \address) { nqp::box_i(address, self) }
    method from(\obj) { nqp::nativecallcast(VMPtr, VMPtr, nqp::decont(obj)) }
    method gist { "\&*{ nqp::unbox_i(self) }" }
    method perl { "VMPtr.from({ nqp::unbox_i(self) })" }
}

proto csizeof(Mu \obj) is export { obj.?CT-SIZEOF // nqp::nativecallsizeof(obj) }
proto ctypeof(Mu \obj) is export { obj.?CT-TYPEOF // {*} }
proto carraytype(Mu) is export {*}
proto cpointer(Mu:U \T, $value, *%) is export {*}
proto carray(Mu:U \T, *@values, *%) is export {*}
proto cval(Mu:U \T, $value, *%) is export {*}
proto cbind(Str $name, Signature $sig, *%) is export {*}
proto cinvoke(Str $name, Signature $sig, *@, *%) is export {*}

my constant PTRSIZE = nqp::nativecallsizeof(VMPtr);

my constant INTMAP = Map.new(
    map { CHAR_BIT * nqp::nativecallsizeof($_) => .HOW.name($_) },
        my native longlong is repr<P6int> is ctype<longlong> {},
        my native long is repr<P6int> is ctype<long> {},
        my native int is repr<P6int> is ctype<int> {},
        my native short is repr<P6int> is ctype<short> {},
        my native char is repr<P6int> is ctype<char> {});

my constant NUMMAP = Map.new(
    map { CHAR_BIT * nqp::nativecallsizeof($_) => .HOW.name($_) },
#        my native longdouble is repr<P6num> is ctype<longdouble> {},
        my native double is repr<P6num> is ctype<double> {},
        my native float is repr<P6num> is ctype<float> {});

my constant &ni = sub check-native-int($_, $size) {
    .HOW.WHAT =:= NativeHOW && .HOW.nativesize($_) == $size
        && !.HOW.unsigned($_);
}

my constant &nu = sub check-native-uint($_, $size) {
    .HOW.WHAT =:= NativeHOW && .HOW.nativesize($_) == $size
        && ?.HOW.unsigned($_);
}

my constant &nn = sub check-native-num($_, $size) {
    .HOW.WHAT =:= NativeHOW && .HOW.nativesize($_) == $size;
}

my subset CChar of Int is export where ni $_, nqp::const::C_TYPE_CHAR;
my subset CShort of Int is export where ni $_, nqp::const::C_TYPE_SHORT;
my subset CInt of Int is export where ni $_, nqp::const::C_TYPE_INT;
my subset CLong of Int is export where ni $_, nqp::const::C_TYPE_LONG;
my subset CLLong of Int is export where ni $_, nqp::const::C_TYPE_LONGLONG;

my subset CUChar of Int is export where nu $_, nqp::const::C_TYPE_CHAR;
my subset CUShort of Int is export where nu $_, nqp::const::C_TYPE_SHORT;
my subset CUInt of Int is export where nu $_, nqp::const::C_TYPE_INT;
my subset CULong of Int is export where nu $_, nqp::const::C_TYPE_LONG;
my subset CULLong of Int is export where nu $_, nqp::const::C_TYPE_LONGLONG;

my subset CInt8 of Int is export where ni $_, 8;
my subset CInt16 of Int is export where ni $_, 16;
my subset CInt32 of Int is export where ni $_, 32;
my subset CInt64 of Int is export where ni $_, 64;
my subset CInt128 of Int is export where ni $_, 128;
my subset CIntX of Int is export where ni $_, 0;

my subset CUInt8 of Int is export where nu $_, 8;
my subset CUInt16 of Int is export where nu $_, 16;
my subset CUInt32 of Int is export where nu $_, 32;
my subset CUInt64 of Int is export where nu $_, 64;
my subset CUInt128 of Int is export where nu $_, 128;
my subset CUIntX of Int is export where nu $_, 0;

my subset CFloat of Num is export where nn $_, nqp::const::C_TYPE_FLOAT;
my subset CDouble of Num is export where nn $_, nqp::const::C_TYPE_DOUBLE;
my subset CLDouble of Num is export where nn $_, nqp::const::C_TYPE_LONGDOUBLE;

my subset CNum32 of Num is export where nn $_, 32;
my subset CNum64 of Num is export where nn $_, 64;
my subset CNumX of Num is export where nn $_, 0;

my subset CPointer of Mu is export where .REPR eq 'CPointer';
my subset CArray of Mu is export where .REPR eq 'CArray';
my subset VMArray of Mu is export where .REPR eq 'VMArray' || .WHAT ~~ Blob;

multi ctypeof(CChar) { 'char' }
multi ctypeof(CShort) { 'short' }
multi ctypeof(CInt) { 'int' }
multi ctypeof(CLong) { 'long' }
multi ctypeof(CLLong) { 'longlong' }

multi ctypeof(CUChar) { 'uchar' }
multi ctypeof(CUShort) { 'ushort' }
multi ctypeof(CUInt) { 'uint' }
multi ctypeof(CULong) { 'ulong' }
multi ctypeof(CULLong) { 'ulonglong' }

multi ctypeof(CInt8) { BEGIN INTMAP<8> // Str }
multi ctypeof(CInt16) { BEGIN INTMAP<16> // Str }
multi ctypeof(CInt32) { BEGIN INTMAP<32> // Str }
multi ctypeof(CInt64) { BEGIN INTMAP<64> // Str }
multi ctypeof(CInt128) { BEGIN INTMAP<128> // Str }

multi ctypeof(CIntX $_) {
    INTMAP{ CHAR_BIT * nqp::nativecallsizeof($_) } // Str;
}

multi ctypeof(CUInt8) { BEGIN INTMAP<8> // Str andthen "u$_" }
multi ctypeof(CUInt16) { BEGIN INTMAP<16> // Str andthen "u$_" }
multi ctypeof(CUInt32) { BEGIN INTMAP<32> // Str andthen "u$_" }
multi ctypeof(CUInt64) { BEGIN INTMAP<64> // Str andthen "u$_" }
multi ctypeof(CUInt128) { BEGIN INTMAP<128> // Str andthen "u$_" }

multi ctypeof(CUIntX $_) {
    (INTMAP{ CHAR_BIT * nqp::nativecallsizeof($_) } // Str) andthen "u$_";
}

multi ctypeof(CFloat) { 'float' }
multi ctypeof(CDouble) { 'double' }
multi ctypeof(CLDouble) { 'longdouble' }

multi ctypeof(CNum32) { BEGIN NUMMAP<32> // Str }
multi ctypeof(CNum64) { BEGIN NUMMAP<64> // Str }

multi ctypeof(CNumX $_) {
    NUMMAP{ CHAR_BIT * nqp::nativecallsizeof($_) } // Str;
}

multi ctypeof(CPointer) { 'cpointer' }
multi ctypeof(CArray) { 'carray' }
multi ctypeof(VMArray) { 'vmarray' }

multi ctypeof(Mu $_) { Str }

multi carray(Mu:U \T, *@values) {
    my uint $n = +@values;
    my $raw := carraytype(T).new;
    my $boxed := $raw.box($n);
    while ($n--) { $raw[$n] = @values[$n] }
    $boxed;
}

multi cval(Mu:U \T, $value, *%) {
    my $array := carraytype(T).new;
    $array[0] = $value;
    cpointer(T, $array);
}

multi cbind(Str $name, Signature $sig, Str :$lib) {
    my $argtypes := nqp::list();
    nqp::push($argtypes, nqp::hash('type', ctypeof(.type)))
        for $sig.params.grep(*.positional);

    # only necessary for Int?
    my $rtype := do given $sig.returns {
        when Int { Int }
        when Num { Num }
        default { $_ }
    }

    my $cs := nqp::create(Callsite);
    nqp::buildnativecall(
        $cs,
        $lib // '',
        $name,
        '', # calling convention
        $argtypes,
        nqp::hash('type', ctypeof($sig.returns)),
    );

    sub (|args) {
        fail "Arguments { args.gist } do not match signature { $sig.gist }"
            unless args ~~ $sig;

        my $args := nqp::list();
        nqp::push($args, .?CT-UNBOX // $_)
            for args.list;

        nqp::nativecall($rtype, $cs, $args);
    }
}

multi cinvoke(Str $name, Signature $sig, Capture $args, Str :$lib) {
    cbind($name, $sig, :$lib).(|$args);
}

multi cinvoke(Str $name, Signature $sig, *@args, Str :$lib) {
    cbind($name, $sig, :$lib).(|@args);
}

my role CPtr[::T = Void] is export {
    has $.raw is box_target;

    method CT-SIZEOF { PTRSIZE }
    method CT-TYPEOF { 'cpointer' }
    method CT-UNBOX { $!raw }

    method from(\obj) { self.new(raw => VMPtr.from(obj)) }
    method Int { nqp::unbox_i($!raw) }
    method hex { "0x{ self.Int.base(16).lc }" }
    method gist { "({ T.^name }*){ self.hex }" }
    method to(Mu:U \type) { CPtr[type].new(:$!raw) }
    method of { T }

    method lv is rw { ScalarRef.new(self) }

    method rv {
        given ~T.REPR {
            when 'CPointer' { # FIXME: use uintptr!
                nqp::box_i(self.to(uint64).rv, T);
            }

            when 'P6int' {
                nqp::nativecallcast(nqp::decont(T), Int, nqp::decont($!raw));
            }

            when 'P6num' {
                nqp::nativecallcast(nqp::decont(T), Num, nqp::decont($!raw));
            }

            default {
                die "Cannot dereference pointers of type { T.^name }";
            }
        }
    }
}

multi cpointer(Mu:U \T, $value) { CPtr[T].from($value) }

my class ScalarRef {
    has $.ptr;
    has $.raw;

    method FETCH { $!raw.AT-POS(0) }
    method STORE(\value) { $!raw.ASSIGN-POS(0, value) }

    method new(CPtr \ptr) {
        once {
            nqp::loadbytecode('nqp.moarvm');
            EVAL q:to/__END__/, :lang<nqp>;
            my $FETCH := nqp::getstaticcode(-> $cont {
                my $var := nqp::p6var($cont);
                nqp::decont(nqp::findmethod($var,'FETCH')($var));
            });

            my $STORE := nqp::getstaticcode(-> $cont, $value {
                my $var := nqp::p6var($cont);
                nqp::findmethod($var, 'STORE')($var, $value);
                Mu;
            });

            my $pair := nqp::hash('fetch', $FETCH, 'store', $STORE);
            nqp::setcontspec(ScalarRef,  'code_pair', $pair);
            Mu;
            __END__
        }

        my \type = nqp::decont(carraytype(ptr.of));
        my \raw = nqp::nativecallcast(type, type, nqp::decont(ptr.raw));
        my \ref = nqp::create(ScalarRef);
        nqp::bindattr(ref, ScalarRef, '$!raw', raw);
        nqp::bindattr(ref, ScalarRef, '$!ptr', ptr);

        ref;
    }
}

my role BoxedArray[Mu:U \T, UInt \elems] does Positional[T] {
    has $.raw handles <AT-POS ASSIGN-POS>;

    method CT-SIZEOF { self.elems * csizeof(T) }
    method CT-TYPEOF { 'carray' }
    method CT-UNBOX { $!raw }

    method ptr { CPtr[T].from($!raw) }
    method elems { elems }

    method iterator {
        my \array = self;
        my uint $elems = elems;
        .new given class :: does Iterator {
            has uint $!i = 0;
            method pull-one {
                $!i < $elems ?? array.AT-POS($!i++) !! IterationEnd;
            }
        }
    }
}

my role RawArray[Mu:U \T] {
    method box($raw: uint $elems) { BoxedArray[T, $elems].new(:$raw) }
}

my role IntegerArray[Mu:U \T] does RawArray[T] {
    method AT-POS(uint \pos) { nqp::atpos_i(self, pos) }
    method ASSIGN-POS(uint \pos, \value) { nqp::bindpos_i(self, pos, value) }
}

my role FloatingArray[Mu:U \T] does RawArray[T] {
    method AT-POS(uint \pos) { nqp::atpos_n(self, pos) }
    method ASSIGN-POS(uint \pos, \value) { nqp::bindpos_n(self, pos, value) }
}

my native cchar is Int is ctype<char> is repr<P6int> is export {}
my class CCharArray is repr<CArray> is array_type(cchar)
    does IntegerArray[cchar] {}
multi carraytype(CChar) { CCharArray }

my native cshort is Int is ctype<short> is repr<P6int> is export {}
my class CShortArray is repr<CArray> is array_type(cshort)
    does IntegerArray[cshort] {}
multi carraytype(CShort) { CShortArray }

my native cint is Int is ctype<int> is repr<P6int> is export {}
my class CIntArray is repr<CArray> is array_type(cint)
    does IntegerArray[cint] {}
multi carraytype(CInt) { CIntArray }
