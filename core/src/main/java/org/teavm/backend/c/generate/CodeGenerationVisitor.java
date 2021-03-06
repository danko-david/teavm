/*
 *  Copyright 2018 Alexey Andreev.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.teavm.backend.c.generate;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.DoubleBuffer;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;
import java.nio.LongBuffer;
import java.nio.ShortBuffer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.teavm.ast.ArrayType;
import org.teavm.ast.AssignmentStatement;
import org.teavm.ast.BinaryExpr;
import org.teavm.ast.BlockStatement;
import org.teavm.ast.BreakStatement;
import org.teavm.ast.CastExpr;
import org.teavm.ast.ConditionalExpr;
import org.teavm.ast.ConditionalStatement;
import org.teavm.ast.ConstantExpr;
import org.teavm.ast.ContinueStatement;
import org.teavm.ast.Expr;
import org.teavm.ast.ExprVisitor;
import org.teavm.ast.GotoPartStatement;
import org.teavm.ast.InitClassStatement;
import org.teavm.ast.InstanceOfExpr;
import org.teavm.ast.InvocationExpr;
import org.teavm.ast.MonitorEnterStatement;
import org.teavm.ast.MonitorExitStatement;
import org.teavm.ast.NewArrayExpr;
import org.teavm.ast.NewExpr;
import org.teavm.ast.NewMultiArrayExpr;
import org.teavm.ast.OperationType;
import org.teavm.ast.PrimitiveCastExpr;
import org.teavm.ast.QualificationExpr;
import org.teavm.ast.ReturnStatement;
import org.teavm.ast.SequentialStatement;
import org.teavm.ast.Statement;
import org.teavm.ast.StatementVisitor;
import org.teavm.ast.SubscriptExpr;
import org.teavm.ast.SwitchClause;
import org.teavm.ast.SwitchStatement;
import org.teavm.ast.ThrowStatement;
import org.teavm.ast.TryCatchStatement;
import org.teavm.ast.UnaryExpr;
import org.teavm.ast.UnwrapArrayExpr;
import org.teavm.ast.VariableExpr;
import org.teavm.ast.WhileStatement;
import org.teavm.backend.c.intrinsic.Intrinsic;
import org.teavm.backend.c.intrinsic.IntrinsicContext;
import org.teavm.backend.c.util.InteropUtil;
import org.teavm.diagnostics.Diagnostics;
import org.teavm.interop.Address;
import org.teavm.interop.c.Variable;
import org.teavm.model.CallLocation;
import org.teavm.model.ClassReader;
import org.teavm.model.ClassReaderSource;
import org.teavm.model.ElementModifier;
import org.teavm.model.FieldReference;
import org.teavm.model.MethodReader;
import org.teavm.model.MethodReference;
import org.teavm.model.TextLocation;
import org.teavm.model.ValueType;
import org.teavm.model.classes.VirtualTable;
import org.teavm.runtime.Allocator;
import org.teavm.runtime.ExceptionHandling;
import org.teavm.runtime.Fiber;
import org.teavm.runtime.RuntimeArray;
import org.teavm.runtime.RuntimeClass;
import org.teavm.runtime.RuntimeObject;

public class CodeGenerationVisitor implements ExprVisitor, StatementVisitor {
    public static final MethodReference ALLOC_METHOD = new MethodReference(Allocator.class,
            "allocate", RuntimeClass.class, Address.class);
    private static final MethodReference ALLOC_ARRAY_METHOD = new MethodReference(Allocator.class,
            "allocateArray", RuntimeClass.class, int.class, Address.class);
    private static final MethodReference ALLOC_MULTI_ARRAY_METHOD = new MethodReference(Allocator.class,
            "allocateMultiArray", RuntimeClass.class, Address.class, int.class, RuntimeArray.class);
    private static final MethodReference THROW_EXCEPTION_METHOD = new MethodReference(ExceptionHandling.class,
            "throwException", Throwable.class, void.class);
    private static final MethodReference MONITOR_ENTER = new MethodReference(Object.class, "monitorEnter",
            Object.class, void.class);
    private static final MethodReference MONITOR_EXIT = new MethodReference(Object.class, "monitorExit",
            Object.class, void.class);
    private static final MethodReference MONITOR_ENTER_SYNC = new MethodReference(Object.class, "monitorEnterSync",
            Object.class, void.class);
    private static final MethodReference MONITOR_EXIT_SYNC = new MethodReference(Object.class, "monitorExitSync",
            Object.class, void.class);

    private static final Map<String, String> BUFFER_TYPES = new HashMap<>();

    private GenerationContext context;
    private NameProvider names;
    private CodeWriter writer;
    private int[] temporaryVariableLevel = new int[5];
    private int[] maxTemporaryVariableLevel = new int[5];
    private MethodReference callingMethod;
    private IncludeManager includes;
    private boolean end;
    private boolean async;
    private final Deque<LocationStackEntry> locationStack = new ArrayDeque<>();

    static {
        BUFFER_TYPES.put(ByteBuffer.class.getName(), "int8_t");
        BUFFER_TYPES.put(ShortBuffer.class.getName(), "int16_t");
        BUFFER_TYPES.put(CharBuffer.class.getName(), "char16_t");
        BUFFER_TYPES.put(IntBuffer.class.getName(), "int32_t");
        BUFFER_TYPES.put(LongBuffer.class.getName(), "int64_t");
        BUFFER_TYPES.put(FloatBuffer.class.getName(), "float");
        BUFFER_TYPES.put(DoubleBuffer.class.getName(), "double");
    }

    public CodeGenerationVisitor(GenerationContext context, CodeWriter writer, IncludeManager includes) {
        this.context = context;
        this.writer = writer;
        this.names = context.getNames();
        this.includes = includes;
    }

    public void setAsync(boolean async) {
        this.async = async;
    }

    public int[] getTemporaries() {
        return maxTemporaryVariableLevel;
    }

    public void setCallingMethod(MethodReference callingMethod) {
        this.callingMethod = callingMethod;
    }

    @Override
    public void visit(BinaryExpr expr) {
        pushLocation(expr.getLocation());
        try {
            switch (expr.getOperation()) {
                case COMPARE:
                    writer.print("teavm_compare_");
                    switch (expr.getType()) {
                        case INT:
                            writer.print("i32");
                            break;
                        case LONG:
                            writer.print("i64");
                            break;
                        case FLOAT:
                            writer.print("float");
                            break;
                        case DOUBLE:
                            writer.print("double");
                            break;
                    }
                    writer.print("(");
                    expr.getFirstOperand().acceptVisitor(this);
                    writer.print(", ");
                    expr.getSecondOperand().acceptVisitor(this);
                    writer.print(")");
                    return;
                case UNSIGNED_RIGHT_SHIFT: {
                    String type = expr.getType() == OperationType.LONG ? "int64_t" : "int32_t";
                    writer.print("((" + type + ") ((u" + type + ") ");

                    expr.getFirstOperand().acceptVisitor(this);
                    writer.print(" >> ");
                    expr.getSecondOperand().acceptVisitor(this);

                    writer.print("))");
                    return;
                }

                case MODULO: {
                    switch (expr.getType()) {
                        case FLOAT:
                            writer.print("fmodf(");
                            expr.getFirstOperand().acceptVisitor(this);
                            writer.print(", ");
                            expr.getSecondOperand().acceptVisitor(this);
                            writer.print(")");
                            return;
                        case DOUBLE:
                            writer.print("fmod(");
                            expr.getFirstOperand().acceptVisitor(this);
                            writer.print(", ");
                            expr.getSecondOperand().acceptVisitor(this);
                            writer.print(")");
                            return;
                        default:
                            break;
                    }
                    break;
                }

                default:
                    break;
            }

            writer.print("(");
            expr.getFirstOperand().acceptVisitor(this);

            String op;
            switch (expr.getOperation()) {
                case ADD:
                    op = "+";
                    break;
                case SUBTRACT:
                    op = "-";
                    break;
                case MULTIPLY:
                    op = "*";
                    break;
                case DIVIDE:
                    op = "/";
                    break;
                case MODULO:
                    op = "%";
                    break;
                case BITWISE_AND:
                    op = "&";
                    break;
                case BITWISE_OR:
                    op = "|";
                    break;
                case BITWISE_XOR:
                    op = "^";
                    break;
                case LEFT_SHIFT:
                    op = "<<";
                    break;
                case RIGHT_SHIFT:
                    op = ">>";
                    break;
                case EQUALS:
                    op = "==";
                    break;
                case NOT_EQUALS:
                    op = "!=";
                    break;
                case GREATER:
                    op = ">";
                    break;
                case GREATER_OR_EQUALS:
                    op = ">=";
                    break;
                case LESS:
                    op = "<";
                    break;
                case LESS_OR_EQUALS:
                    op = "<=";
                    break;
                case AND:
                    op = "&&";
                    break;
                case OR:
                    op = "||";
                    break;
                default:
                    throw new AssertionError();
            }

            writer.print(" ").print(op).print(" ");
            expr.getSecondOperand().acceptVisitor(this);
            writer.print(")");
        } finally {
            popLocation(expr.getLocation());
        }
    }

    @Override
    public void visit(UnaryExpr expr) {
        pushLocation(expr.getLocation());
        switch (expr.getOperation()) {
            case NOT:
                writer.print("(");
                writer.print("!");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
            case NEGATE:
                writer.print("(");
                writer.print("-");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
            case LENGTH:
                writer.print("TEAVM_ARRAY_LENGTH(");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
            case NULL_CHECK:
                expr.getOperand().acceptVisitor(this);
                break;
            case INT_TO_BYTE:
                writer.print("TEAVM_TO_BYTE(");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
            case INT_TO_SHORT:
                writer.print("TEAVM_TO_SHORT(");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
            case INT_TO_CHAR:
                writer.print("TEAVM_TO_CHAR(");
                expr.getOperand().acceptVisitor(this);
                writer.print(")");
                break;
        }
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(ConditionalExpr expr) {
        pushLocation(expr.getLocation());
        writer.print("(");
        expr.getCondition().acceptVisitor(this);
        writer.print(" ? ");
        expr.getConsequent().acceptVisitor(this);
        writer.print(" : ");
        expr.getAlternative().acceptVisitor(this);
        writer.print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(ConstantExpr expr) {
        pushLocation(expr.getLocation());
        CodeGeneratorUtil.writeValue(writer, context, includes, expr.getValue());
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(VariableExpr expr) {
        pushLocation(expr.getLocation());
        writer.print(getVariableName(expr.getIndex()));
        popLocation(expr.getLocation());
    }

    private String getVariableName(int index) {
        if (index == 0) {
            return "teavm_this_";
        } else {
            return "teavm_local_" + index;
        }
    }

    @Override
    public void visit(SubscriptExpr expr) {
        pushLocation(expr.getLocation());
        writer.print("TEAVM_ARRAY_AT(");
        expr.getArray().acceptVisitor(this);
        writer.print(", ").print(getArrayType(expr.getType())).print(", ");
        expr.getIndex().acceptVisitor(this);
        writer.print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(UnwrapArrayExpr expr) {
        pushLocation(expr.getLocation());
        expr.getArray().acceptVisitor(this);
        popLocation(expr.getLocation());
    }

    private static String getArrayType(ArrayType type) {
        switch (type) {
            case BYTE:
                return "int8_t";
            case SHORT:
                return "int16_t";
            case CHAR:
                return "char16_t";
            case INT:
                return "int32_t";
            case LONG:
                return "int64_t";
            case FLOAT:
                return "float";
            case DOUBLE:
                return "double";
            case OBJECT:
                return "void*";
            default:
                throw new AssertionError();
        }
    }

    @Override
    public void visit(InvocationExpr expr) {
        ClassReader cls = context.getClassSource().get(expr.getMethod().getClassName());
        if (cls != null) {
            InteropUtil.processInclude(cls.getAnnotations(), includes);
            MethodReader method = cls.getMethod(expr.getMethod().getDescriptor());
            if (method != null) {
                InteropUtil.processInclude(method.getAnnotations(), includes);
            }
        }

        Intrinsic intrinsic = context.getIntrinsic(expr.getMethod());
        if (intrinsic != null) {
            pushLocation(expr.getLocation());
            intrinsic.apply(intrinsicContext, expr);
            popLocation(expr.getLocation());
            return;
        }

        pushLocation(expr.getLocation());
        switch (expr.getType()) {
            case CONSTRUCTOR:
                generateCallToConstructor(expr.getMethod(), expr.getArguments());
                break;

            case SPECIAL:
            case STATIC:
                generateDirectCall(expr.getMethod(), expr.getArguments());
                break;

            case DYNAMIC: {
                generateVirtualCall(expr.getMethod(), expr.getArguments());
                break;
            }
        }

        popLocation(expr.getLocation());
    }

    private void generateCallToConstructor(MethodReference reference, List<? extends Expr> arguments) {
        String receiver = allocTemporaryVariable(CVariableType.PTR);
        writer.print("(" + receiver + " = ");
        allocObject(reference.getClassName());
        writer.print(", ");

        MethodReader method = context.getClassSource().resolve(reference);
        if (method != null) {
            reference = method.getReference();
        }

        includes.includeClass(reference.getClassName());
        writer.print(names.forMethod(reference));

        writer.print("(" + receiver);
        for (Expr arg : arguments) {
            writer.print(", ");
            arg.acceptVisitor(this);
        }
        writer.print("), " + receiver + ")");

        freeTemporaryVariable(CVariableType.PTR);
    }

    private void generateDirectCall(MethodReference reference, List<? extends Expr> arguments) {
        MethodReader method = context.getClassSource().resolve(reference);
        if (method != null && isWrappedNativeCall(method)) {
            generateWrappedNativeCall(method, arguments);
        } else {
            if (method == null || method.hasModifier(ElementModifier.ABSTRACT)) {
                generateNoMethodCall(reference, arguments);
                return;
            }

            reference = method.getReference();
            includes.includeClass(reference.getClassName());
            writer.print(names.forMethod(reference));

            writer.print("(");
            if (!arguments.isEmpty()) {
                arguments.get(0).acceptVisitor(this);
                for (int i = 1; i < arguments.size(); ++i) {
                    writer.print(", ");
                    arguments.get(i).acceptVisitor(this);
                }
            }
            writer.print(")");
        }
    }

    private void generateVirtualCall(MethodReference reference, List<? extends Expr> arguments) {
        VirtualTable vtable = context.getVirtualTableProvider().lookup(reference.getClassName());
        String vtableClass = null;
        if (vtable != null) {
            VirtualTable containingVt = vtable.findMethodContainer(reference.getDescriptor());
            if (containingVt != null) {
                vtableClass = containingVt.getClassName();
            }
        }
        if (vtableClass == null) {
            generateNoMethodCall(reference, arguments);
            return;
        }

        Expr receiverArg = arguments.get(0);
        boolean closingParenthesis = false;
        String receiver;
        if (receiverArg instanceof VariableExpr) {
            receiver = getVariableName(((VariableExpr) receiverArg).getIndex());
        } else {
            receiver = allocTemporaryVariable(CVariableType.PTR);
            writer.print("((").print(receiver).print(" = ");
            arguments.get(0).acceptVisitor(this);
            writer.print("), ");
            closingParenthesis = true;
        }

        includes.includeClass(vtableClass);
        writer.print("TEAVM_METHOD(")
                .print(receiver).print(", ")
                .print(names.forClassClass(vtableClass)).print(", ")
                .print(names.forVirtualMethod(reference.getDescriptor()))
                .print(")(").print(receiver);
        for (int i = 1; i < arguments.size(); ++i) {
            writer.print(", ");
            arguments.get(i).acceptVisitor(this);
        }
        writer.print(")");
        if (closingParenthesis) {
            writer.print(")");
            freeTemporaryVariable(CVariableType.PTR);
        }
    }

    private void generateNoMethodCall(MethodReference reference, List<? extends Expr> arguments) {
        writer.print("(");
        for (Expr arg : arguments) {
            arg.acceptVisitor(this);
            writer.print(", ");
        }
        printDefaultValue(reference.getReturnType());
        writer.print(")");
    }

    private void generateWrappedNativeCall(MethodReader method, List<? extends Expr> arguments) {
        List<String> temporaries = new ArrayList<>();
        List<String> stringTemporaries = new ArrayList<>();
        String resultTmp = null;
        if (method.getResultType() != ValueType.VOID) {
            resultTmp = allocTemporaryVariable(typeToCType(method.getResultType()));
        }

        for (int i = 0; i < arguments.size(); ++i) {
            temporaries.add(allocTemporaryVariable(parameterTypeForCall(method, i)));
        }
        boolean stringResult = method.getResultType().isObject(String.class);

        writer.print("(");
        for (int i = 0; i < arguments.size(); ++i) {
            String tmp = temporaries.get(i);
            writer.print(tmp + " = ");
            ValueType type = method.hasModifier(ElementModifier.STATIC)
                    ? method.parameterType(i)
                    : i == 0 ? ValueType.object(method.getOwnerName()) : method.parameterType(i - 1);
            if (type.isObject(String.class)) {
                writer.print("teavm_stringToC(");
                arguments.get(i).acceptVisitor(this);
                writer.print(")");
                stringTemporaries.add(tmp);
            } else if (isPrimitiveArray(type)) {
                writer.print("TEAVM_ARRAY_DATAN(");
                arguments.get(i).acceptVisitor(this);
                writer.print(", ").printStrictType(((ValueType.Array) type).getItemType()).print(")");
            } else if (isPrimitiveBuffer(type)) {
                writer.print("TEAVM_ARRAY_DATA(TEAVM_FIELD(");
                String typeName = ((ValueType.Object) type).getClassName();
                arguments.get(i).acceptVisitor(this);
                includes.includeClass(typeName);
                writer.print(", ").print(names.forClass(typeName)).print(", ")
                        .print(names.forMemberField(new FieldReference(typeName, "array"))).print(")");
                writer.print(", ").print(BUFFER_TYPES.get(typeName)).print(")");
            } else {
                arguments.get(i).acceptVisitor(this);
            }

            writer.print(", ");
        }

        if (resultTmp != null) {
            writer.print(resultTmp + " = ");
        }
        writer.print(names.forMethod(method.getReference()));
        if (method.getAnnotations().get(Variable.class.getName()) == null) {
            writer.print("(");
            for (int i = 0; i < temporaries.size(); ++i) {
                if (i > 0) {
                    writer.print(", ");
                }
                writer.print(temporaries.get(i));
                freeTemporaryVariable(parameterTypeForCall(method, i));
            }
            writer.print(")");
        } else if (method.parameterCount() > 0 || method.getResultType() == ValueType.VOID) {
            context.getDiagnostics().error(new CallLocation(method.getReference()),
                    "'@Variable' annotation is not applicable to method {{m0}}", method.getReference());
        }

        for (String tmp : stringTemporaries) {
            writer.print(", teavm_free(" + tmp + ")");
        }

        if (resultTmp != null) {
            writer.print(", ");
            if (stringResult) {
                writer.print("teavm_cToString(");
            }
            writer.print(resultTmp);
            if (stringResult) {
                writer.print(")");
            }
            freeTemporaryVariable(typeToCType(method.getResultType()));
        }

        writer.print(")");
    }

    private CVariableType parameterTypeForCall(MethodReader method, int index) {
        if (method.hasModifier(ElementModifier.STATIC)) {
            return typeToCType(method.parameterType(index));
        } else {
            return index == 0 ? CVariableType.PTR : typeToCType(method.parameterType(index - 1));
        }
    }

    private static boolean isPrimitiveArray(ValueType type) {
        if (!(type instanceof ValueType.Array)) {
            return false;
        }

        return ((ValueType.Array) type).getItemType() instanceof ValueType.Primitive;
    }

    private static boolean isPrimitiveBuffer(ValueType type) {
        if (!(type instanceof ValueType.Object)) {
            return false;
        }
        return BUFFER_TYPES.containsKey(((ValueType.Object) type).getClassName());
    }

    private boolean isWrappedNativeCall(MethodReader method) {
        if (!method.hasModifier(ElementModifier.NATIVE)) {
            return false;
        }
        if (method.getAnnotations().get(Variable.class.getName()) != null) {
            return true;
        }
        for (ValueType type : method.getParameterTypes()) {
            if (type.isObject(String.class) || isPrimitiveArray(type) || isPrimitiveBuffer(type)) {
                return true;
            }
        }
        if (method.getResultType().isObject(String.class)) {
            return true;
        }
        return false;
    }

    private String allocTemporaryVariable(CVariableType type) {
        int index = type.ordinal();
        int result = temporaryVariableLevel[index]++;
        maxTemporaryVariableLevel[index] = Math.max(maxTemporaryVariableLevel[index], temporaryVariableLevel[index]);
        return "teavm_tmp_" + type.name().toLowerCase() + "_" + result;
    }

    private void freeTemporaryVariable(CVariableType type) {
        temporaryVariableLevel[type.ordinal()]--;
    }

    private void printDefaultValue(ValueType type) {
        if (type instanceof ValueType.Primitive) {
            writer.print("0");
        } else {
            writer.print("NULL");
        }
    }

    @Override
    public void visit(QualificationExpr expr) {
        FieldReference field = expr.getField();
        if (isMonitorField(field)) {
            pushLocation(expr.getLocation());
            String tmp = allocTemporaryVariable(CVariableType.INT);
            writer.print("(" + tmp + " = TEAVM_FIELD(");
            expr.getQualified().acceptVisitor(this);
            field = new FieldReference(RuntimeObject.class.getName(), "hashCode");
            writer.print(", ").print(names.forClass(field.getClassName()) + ", "
                    + names.forMemberField(field) + ")");
            writer.print(", TEAVM_UNPACK_MONITOR(" + tmp + "))");
            popLocation(expr.getLocation());
            return;
        }

        pushLocation(expr.getLocation());
        printFieldRef(expr.getQualified(), field);
        popLocation(expr.getLocation());
    }

    private void printFieldRef(Expr qualified, FieldReference field) {
        if (qualified != null) {
            ClassReader cls = context.getClassSource().get(field.getClassName());
            writer.print("TEAVM_FIELD(");
            qualified.acceptVisitor(this);
            if (cls != null && isNative(cls)) {
                InteropUtil.processInclude(cls.getAnnotations(), includes);
                writer.print(", ").print(InteropUtil.getNativeName(cls))
                        .print(", ").print(InteropUtil.getNativeName(cls, field.getFieldName()));
            } else {
                includes.includeClass(field.getClassName());
                writer.print(", ").print(names.forClass(field.getClassName()))
                        .print(", ").print(names.forMemberField(field));
            }
            writer.print(")");
        } else {
            includes.includeClass(field.getClassName());
            writer.print(names.forStaticField(field));
        }
    }

    private boolean isNative(ClassReader cls) {
        return context.getCharacteristics().isStructure(cls.getName()) && InteropUtil.isNative(cls);
    }

    private boolean isMonitorField(FieldReference field) {
        return field.getClassName().equals("java.lang.Object") && field.getFieldName().equals("monitor");
    }

    @Override
    public void visit(NewExpr expr) {
        pushLocation(expr.getLocation());
        includes.includeClass(expr.getConstructedClass());
        includes.includeClass(ALLOC_METHOD.getClassName());
        allocObject(expr.getConstructedClass());
        popLocation(expr.getLocation());
    }

    private void allocObject(String className) {
        writer.print(names.forMethod(ALLOC_METHOD)).print("(&")
                .print(names.forClassInstance(ValueType.object(className)))
                .print(")");
    }

    @Override
    public void visit(NewArrayExpr expr) {
        pushLocation(expr.getLocation());
        ValueType type = ValueType.arrayOf(expr.getType());
        writer.print(names.forMethod(ALLOC_ARRAY_METHOD)).print("(&")
                .print(names.forClassInstance(type)).print(", ");
        includes.includeClass(ALLOC_ARRAY_METHOD.getClassName());
        includes.includeType(type);
        expr.getLength().acceptVisitor(this);
        writer.print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(NewMultiArrayExpr expr) {
        writer.print(names.forMethod(ALLOC_MULTI_ARRAY_METHOD)).print("(&")
                .print(names.forClassInstance(expr.getType())).print(", ");
        includes.includeClass(ALLOC_ARRAY_METHOD.getClassName());
        includes.includeType(expr.getType());

        writer.print("(int32_t[]) {");
        expr.getDimensions().get(0).acceptVisitor(this);
        for (int i = 1; i < expr.getDimensions().size(); ++i) {
            writer.print(", ");
            expr.getDimensions().get(i).acceptVisitor(this);
        }

        writer.print("}, ").print(String.valueOf(expr.getDimensions().size())).print(")");
    }

    @Override
    public void visit(InstanceOfExpr expr) {
        pushLocation(expr.getLocation());
        writer.print("teavm_instanceof(");
        expr.getExpr().acceptVisitor(this);
        includes.includeType(expr.getType());
        writer.print(", ").print(names.forSupertypeFunction(expr.getType())).print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(CastExpr expr) {
        if (expr.getTarget() instanceof ValueType.Object) {
            String className = ((ValueType.Object) expr.getTarget()).getClassName();
            if (context.getCharacteristics().isStructure(className)
                    || className.equals(Address.class.getName())) {
                expr.getValue().acceptVisitor(this);
                return;
            }
        }
        pushLocation(expr.getLocation());
        writer.print("teavm_checkcast(");
        expr.getValue().acceptVisitor(this);
        includes.includeType(expr.getTarget());
        writer.print(", ").print(names.forSupertypeFunction(expr.getTarget())).print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(PrimitiveCastExpr expr) {
        pushLocation(expr.getLocation());
        writer.print("((");
        switch (expr.getTarget()) {
            case INT:
                writer.print("int32_t");
                break;
            case LONG:
                writer.print("int64_t");
                break;
            case FLOAT:
                writer.print("float");
                break;
            case DOUBLE:
                writer.print("double");
                break;
        }
        writer.print(") ");
        expr.getValue().acceptVisitor(this);
        writer.print(")");
        popLocation(expr.getLocation());
    }

    @Override
    public void visit(AssignmentStatement statement) {
        pushLocation(statement.getLocation());
        if (statement.getLeftValue() != null) {
            if (statement.getLeftValue() instanceof QualificationExpr) {
                QualificationExpr qualification = (QualificationExpr) statement.getLeftValue();
                FieldReference field = qualification.getField();
                if (isMonitorField(field)) {
                    writer.print("TEAVM_FIELD(");
                    qualification.getQualified().acceptVisitor(this);
                    field = new FieldReference(RuntimeObject.class.getName(), "hashCode");
                    writer.print(", ").print(names.forClass(field.getClassName()) + ", "
                            + names.forMemberField(field) + ") = TEAVM_PACK_MONITOR(");
                    statement.getRightValue().acceptVisitor(this);
                    writer.println(");");
                    popLocation(statement.getLocation());
                    return;
                }
            }

            statement.getLeftValue().acceptVisitor(this);
            writer.print(" = ");
        }
        statement.getRightValue().acceptVisitor(this);
        writer.println(";");

        if (statement.isAsync()) {
            emitSuspendChecker();
        }

        popLocation(statement.getLocation());
    }

    @Override
    public void visit(SequentialStatement statement) {
        visitMany(statement.getSequence());
    }

    private void visitMany(List<Statement> statements) {
        if (statements.isEmpty()) {
            return;
        }
        boolean oldEnd = end;
        for (int i = 0; i < statements.size() - 1; ++i) {
            end = false;
            statements.get(i).acceptVisitor(this);
        }
        end = oldEnd;
        statements.get(statements.size() - 1).acceptVisitor(this);
        end = oldEnd;
    }

    @Override
    public void visit(ConditionalStatement statement) {
        while (true) {
            pushLocation(statement.getCondition().getLocation());
            writer.print("if (");
            statement.getCondition().acceptVisitor(this);
            writer.println(") {").indent();
            popLocation(statement.getCondition().getLocation());

            visitMany(statement.getConsequent());
            writer.outdent().print("}");

            if (statement.getAlternative().isEmpty()) {
                writer.println();
                break;
            }

            writer.print(" else ");
            if (statement.getAlternative().size() == 1
                    && statement.getAlternative().get(0) instanceof ConditionalStatement) {
                statement = (ConditionalStatement) statement.getAlternative().get(0);
            } else {
                writer.println("{").indent();
                visitMany(statement.getAlternative());
                writer.outdent().println("}");
                break;
            }
        }
    }

    @Override
    public void visit(SwitchStatement statement) {
        pushLocation(statement.getValue().getLocation());
        writer.print("switch (");
        statement.getValue().acceptVisitor(this);
        writer.print(") {").println().indent();
        popLocation(statement.getValue().getLocation());

        for (SwitchClause clause : statement.getClauses()) {
            for (int condition : clause.getConditions()) {
                writer.println("case " + condition + ":");
            }

            writer.indent();
            boolean oldEnd = end;
            for (Statement part : clause.getBody()) {
                end = false;
                part.acceptVisitor(this);
            }
            end = oldEnd;
            writer.outdent();
        }

        if (!statement.getDefaultClause().isEmpty()) {
            writer.println("default:").indent();
            visitMany(statement.getDefaultClause());
            writer.outdent();
        }

        writer.outdent().println("}");

        if (statement.getId() != null) {
            writer.outdent().println("teavm_label_" + statement.getId() + ":;").indent();
        }
    }

    @Override
    public void visit(WhileStatement statement) {
        writer.print("while (");
        if (statement.getCondition() != null) {
            statement.getCondition().acceptVisitor(this);
        } else {
            writer.print("1");
        }
        writer.println(") {").indent();

        boolean oldEnd = end;
        for (Statement part : statement.getBody()) {
            end = false;
            part.acceptVisitor(this);
        }
        end = oldEnd;

        if (statement.getId() != null) {
            writer.outdent().println("teavm_cnt_" + statement.getId() + ":;").indent();
        }
        writer.outdent().println("}");

        if (statement.getId() != null) {
            writer.outdent().println("teavm_label_" + statement.getId() + ":;").indent();
        }
    }

    @Override
    public void visit(BlockStatement statement) {
        visitMany(statement.getBody());

        if (statement.getId() != null) {
            writer.outdent().println("teavm_label_" + statement.getId() + ":;").indent();
        }
    }

    @Override
    public void visit(BreakStatement statement) {
        pushLocation(statement.getLocation());
        if (statement.getTarget() == null || statement.getTarget().getId() == null) {
            writer.println("break;");
        } else {
            writer.println("goto teavm_label_" + statement.getTarget().getId() + ";");
        }
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(ContinueStatement statement) {
        pushLocation(statement.getLocation());
        if (statement.getTarget() == null || statement.getTarget().getId() == null) {
            writer.println("continue;");
        } else {
            writer.println("goto teavm_cnt_" + statement.getTarget().getId() + ";");
        }
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(ReturnStatement statement) {
        pushLocation(statement.getLocation());
        writer.print("return");
        if (statement.getResult() != null) {
            writer.print(" ");
            statement.getResult().acceptVisitor(this);
        }
        writer.println(";");
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(ThrowStatement statement) {
        pushLocation(statement.getLocation());
        includes.includeClass(THROW_EXCEPTION_METHOD.getClassName());
        writer.print(names.forMethod(THROW_EXCEPTION_METHOD)).print("(");
        statement.getException().acceptVisitor(this);
        writer.println(");");
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(InitClassStatement statement) {
        pushLocation(statement.getLocation());
        includes.includeClass(statement.getClassName());
        writer.println(names.forClassInitializer(statement.getClassName()) + "();");
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(TryCatchStatement statement) {
    }

    @Override
    public void visit(GotoPartStatement statement) {
    }

    @Override
    public void visit(MonitorEnterStatement statement) {
        pushLocation(statement.getLocation());
        includes.includeClass("java.lang.Object");
        writer.print(names.forMethod(async ? MONITOR_ENTER : MONITOR_ENTER_SYNC)).print("(");
        statement.getObjectRef().acceptVisitor(this);
        writer.println(");");
        popLocation(statement.getLocation());
    }

    @Override
    public void visit(MonitorExitStatement statement) {
        pushLocation(statement.getLocation());
        includes.includeClass("java.lang.Object");
        writer.print(names.forMethod(async ? MONITOR_EXIT : MONITOR_EXIT_SYNC)).print("(");
        statement.getObjectRef().acceptVisitor(this);
        writer.println(");");
        popLocation(statement.getLocation());
    }

    public void emitSuspendChecker() {
        String suspendingName = names.forMethod(new MethodReference(Fiber.class, "isSuspending", boolean.class));
        writer.println("if (" + suspendingName + "(fiber)) goto teavm_exit_loop;");
    }

    private IntrinsicContext intrinsicContext = new IntrinsicContext() {
        @Override
        public CodeWriter writer() {
            return writer;
        }

        @Override
        public NameProvider names() {
            return names;
        }

        @Override
        public void emit(Expr expr) {
            expr.acceptVisitor(CodeGenerationVisitor.this);
        }

        @Override
        public Diagnostics diagnotics() {
            return context.getDiagnostics();
        }

        @Override
        public MethodReference callingMethod() {
            return callingMethod;
        }

        @Override
        public StringPool stringPool() {
            return context.getStringPool();
        }

        @Override
        public IncludeManager includes() {
            return includes;
        }

        @Override
        public String escapeFileName(String name) {
            StringBuilder sb = new StringBuilder();
            ClassGenerator.escape(name, sb);
            return sb.toString();
        }

        @Override
        public boolean isIncremental() {
            return context.isIncremental();
        }

        @Override
        public ClassReaderSource classes() {
            return context.getClassSource();
        }
    };

    private static CVariableType typeToCType(ValueType type) {
        if (type instanceof ValueType.Primitive) {
            switch (((ValueType.Primitive) type).getKind()) {
                case BOOLEAN:
                case CHARACTER:
                case BYTE:
                case SHORT:
                case INTEGER:
                    return CVariableType.INT;
                case LONG:
                    return CVariableType.LONG;
                case FLOAT:
                    return CVariableType.FLOAT;
                case DOUBLE:
                    return CVariableType.DOUBLE;
            }
        }
        return CVariableType.PTR;
    }

    private void pushLocation(TextLocation location) {
        if (location == null) {
            return;
        }
        LocationStackEntry prevEntry = locationStack.peek();
        if (prevEntry == null || !location.equals(prevEntry.location)) {
            if (location.getFileName() == null) {
                writer.nosource();
            } else {
                writer.source(location.getFileName(), location.getLine());
            }
        }
        locationStack.push(new LocationStackEntry(location));
    }

    private void popLocation(TextLocation location) {
        if (location == null) {
            return;
        }
        LocationStackEntry prevEntry = locationStack.pop();
        LocationStackEntry entry = locationStack.peek();
        if (entry != null) {
            if (!entry.location.equals(prevEntry.location)) {
                if (entry.location.getFileName() == null) {
                    writer.nosource();
                } else {
                    writer.source(entry.location.getFileName(), entry.location.getLine());
                }
            }
        } else {
            writer.nosource();
        }
    }

    static class LocationStackEntry {
        final TextLocation location;

        LocationStackEntry(TextLocation location) {
            this.location = location;
        }
    }
}
