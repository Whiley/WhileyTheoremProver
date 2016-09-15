package wycs.io;

import java.io.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import wyautl.core.Automaton;
import wyautl.io.BinaryAutomataWriter;
import wybs.lang.NameID;
import wyfs.io.BinaryOutputStream;
import wyfs.lang.Path;
import wycs.lang.*;
import wycs.lang.SyntaxTree.Location;
import wycs.util.AbstractBytecode;

public class WycsFileWriter {
	private static final int MAJOR_VERSION = 0;
	private static final int MINOR_VERSION = 1;

	private BinaryOutputStream out;

	private final ArrayList<String> stringPool  = new ArrayList<String>();
	private final HashMap<String,Integer> stringCache = new HashMap<String,Integer>();
	private final ArrayList<PATH_Item> pathPool = new ArrayList<PATH_Item>();
	private final HashMap<Path.ID,Integer> pathCache = new HashMap<Path.ID,Integer>();
	private final ArrayList<NAME_Item> namePool = new ArrayList<NAME_Item>();
	private final HashMap<NameID,Integer> nameCache = new HashMap<NameID,Integer>();
	private final ArrayList<Value> constantPool = new ArrayList<Value>();
	private final HashMap<Value,Integer> constantCache = new HashMap<Value,Integer>();
	private final ArrayList<SemanticType> typePool = new ArrayList<SemanticType>();
	private final HashMap<SemanticType,Integer> typeCache = new HashMap<SemanticType,Integer>();

	public WycsFileWriter(OutputStream output) {
		this.out = new BinaryOutputStream(output);
	}

	public void write(WycsFile module) throws IOException {
		// first, write magic number
		out.write_u8(0x57); // W
		out.write_u8(0x59); // Y
		out.write_u8(0x43); // C
		out.write_u8(0x53); // S
		out.write_u8(0x46); // F
		out.write_u8(0x49); // I
		out.write_u8(0x4C); // L
		out.write_u8(0x45); // E

		// second, build pools
		buildPools(module);

		// third, write head block
		writeBlock(BLOCK_Header,module,out);

		// fourth, write module block(s)
		writeBlock(BLOCK_Module,module,out);

		out.flush();
	}

	private void writeBlock(int kind, Object data, BinaryOutputStream output)
			throws IOException {

		output.pad_u8(); // pad out to next byte boundary

		// determine bytes for block
		byte[] bytes = null;
		switch(kind) {
			case BLOCK_Header:
				bytes = generateHeaderBlock((WycsFile) data);
				break;
			case BLOCK_Module:
				bytes = generateModuleBlock((WycsFile) data);
				break;
			case BLOCK_Macro:
				bytes = generateMacroBlock((WycsFile.Macro) data);
				break;
			case BLOCK_Function:
				bytes = generateFunctionBlock((WycsFile.Function) data);
				break;
			case BLOCK_Type:
				bytes = generateTypeBlock((WycsFile.Type) data);
				break;
			case BLOCK_Assert:
				bytes = generateAssertBlock((WycsFile.Assert) data);
				break;
		}

		output.write_uv(kind);
		output.write_uv(bytes.length);
		output.pad_u8(); // pad out to next byte boundary
		output.write(bytes);
	}

	/**
	 * Write the header information for this WYCS file, including the stratified
	 * resource pool.
	 *
	 * @param module
	 *
	 * @throws IOException
	 */
	private byte[] generateHeaderBlock(WycsFile module)
			throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);

		// second, write the file version number
		output.write_uv(MAJOR_VERSION);
		output.write_uv(MINOR_VERSION);

		// third, write the various pool sizes
		output.write_uv(stringPool.size());
		output.write_uv(pathPool.size());
		output.write_uv(namePool.size());
		output.write_uv(typePool.size());
		output.write_uv(constantPool.size());

		// finally, write the number of remaining blocks
		output.write_uv(module.getDeclarations().size());

		writeStringPool(output);
		writePathPool(output);
		writeNamePool(output);
		writeTypePool(output);
		writeConstantPool(output);

		output.close();

		return bytes.toByteArray();
	}

	private byte[] generateModuleBlock(WycsFile module) throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);

		output.write_uv(pathCache.get(module.getEntry().id())); // FIXME: BROKEN!
		output.write_uv(module.getDeclarations().size());

		for (WycsFile.Declaration d : module.getDeclarations()) {
			writeModuleBlock(d, output);
		}

		output.close();

		return bytes.toByteArray();
	}

	/**
	 * Write the list of strings making up the string pool in UTF8.
	 *
	 * @throws IOException
	 */
	private void writeStringPool(BinaryOutputStream output) throws IOException {
		//System.out.println("Writing " + stringPool.size() + " string item(s).");
		for (String s : stringPool) {
			try {
				byte[] bytes = s.getBytes("UTF-8");
				output.write_uv(bytes.length);
				output.write(bytes, 0, bytes.length);
			} catch (UnsupportedEncodingException e) {
				// hmmm, this aint pretty ;)
			}
		}
	}

	private void writePathPool(BinaryOutputStream output) throws IOException {
		for(int i=1;i<pathPool.size();++i) {
			PATH_Item p = pathPool.get(i);
			output.write_uv(p.parentIndex);
			output.write_uv(p.stringIndex);
		}
	}

	private void writeNamePool(BinaryOutputStream output) throws IOException {
		//System.out.println("Writing " + stringPool.size() + " name item(s).");
		for (NAME_Item p : namePool) {
			//output.write_uv(p.kind.kind());
			output.write_uv(p.pathIndex);
			output.write_uv(p.nameIndex);
		}
	}

	private void writeConstantPool(BinaryOutputStream output) throws IOException {
		// System.out.println("Writing " + constantPool.size() + " constant item(s).");

		for (Value val : constantPool) {
			if(val instanceof Value.Null) {
				Value.Null b = (Value.Null) val;
				output.write_uv(CONSTANT_Null);
			} else if(val instanceof Value.Bool) {
				Value.Bool b = (Value.Bool) val;
				output.write_uv(b.value ? CONSTANT_True : CONSTANT_False);
			} else if(val instanceof Value.Integer) {
				Value.Integer i = (Value.Integer) val;
				BigInteger num = i.value;
				byte[] numbytes = num.toByteArray();
				output.write_uv(CONSTANT_Int);
				output.write_uv(numbytes.length);
				output.write(numbytes);
			} else if(val instanceof Value.String) {
				Value.String s = (Value.String) val;
				output.write_uv(CONSTANT_String);
				String value = s.value;
				output.write_uv(stringCache.get(value));

			} else if(val instanceof Value.Decimal) {
				Value.Decimal r = (Value.Decimal) val;
				output.write_uv(CONSTANT_Real);
				BigInteger mantissa = r.value.unscaledValue();
				int exponent = r.value.scale();
				byte[] bytes = mantissa.toByteArray();
				output.write_uv(bytes.length);
				output.write(bytes);
				output.write_uv(exponent);

			} else if(val instanceof Value.Array) {
				Value.Array s = (Value.Array) val;
				output.write_uv(CONSTANT_Array);
				output.write_uv(s.values.size());
				for(Value v : s.values) {
					int index = constantCache.get(v);
					output.write_uv(index);
				}

			} else if(val instanceof Value.Tuple) {
				Value.Tuple t = (Value.Tuple) val;
				output.write_uv(CONSTANT_Tuple);
				output.write_uv(t.values.size());
				for(Value v : t.values) {
					int index = constantCache.get(v);
					output.write_uv(index);
				}
			} else {
				throw new RuntimeException("Unknown value encountered - " + val);
			}
		}
	}

	private void writeTypePool(BinaryOutputStream output) throws IOException {
		// First, we accumulate the automata for all types in the pool into one
		// automaton. This helps reduce the amount of redundancy between types.
		Automaton global = new Automaton();
		for (int i = 0; i != typePool.size(); ++i) {
			Automaton automaton = typePool.get(i).automaton();
			int root = global.addAll(automaton.getRoot(0), automaton);
			global.setRoot(i, root);
		}

		global.minimise();
		global.compact(0);
		// FIXME: put this back in!!
		// global.canonicalise();

		// Second, we write the single global automaton to the output stream.
		BinaryAutomataWriter writer = new BinaryAutomataWriter(output,
				Types.SCHEMA);
		writer.write(global);
	}

	private void writeModuleBlock(WycsFile.Declaration d,
			BinaryOutputStream output) throws IOException {
		if(d instanceof WycsFile.Macro) {
			writeBlock(BLOCK_Macro, d ,output);
		} else if(d instanceof WycsFile.Type) {
			writeBlock(BLOCK_Type, d ,output);
		} else if(d instanceof WycsFile.Function) {
			writeBlock(BLOCK_Function, d, output);
		} else if(d instanceof WycsFile.Assert) {
			writeBlock(BLOCK_Assert, d, output);
		}
	}

	private byte[] generateMacroBlock(WycsFile.Macro md) throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);

		output.write_uv(stringCache.get(md.getName()));
		output.write_uv(typeCache.get(md.getType()));
		output.write_uv(md.getBody().getIndex());
		writeSyntaxTree(md.getTree(),output);

		output.close();
		return bytes.toByteArray();
	}

	private byte[] generateTypeBlock(WycsFile.Type md) throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);
		List<Location<?>> invariant = md.getInvariant();
		//
		output.write_uv(stringCache.get(md.getName()));
		output.write_uv(typeCache.get(md.getType()));
		output.write_uv(invariant.size());
		//
		for(int i=0;i!=invariant.size();++i) {
			output.write_uv(invariant.get(i).getIndex());
		}
		//
		writeSyntaxTree(md.getTree(),output);
		//
		output.close();
		return bytes.toByteArray();
	}

	private byte[] generateFunctionBlock(WycsFile.Function fd) throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);

		output.write_uv(stringCache.get(fd.getName()));
		output.write_uv(typeCache.get(fd.getType()));

		output.close();
		return bytes.toByteArray();
	}

	private byte[] generateAssertBlock(WycsFile.Assert td) throws IOException {
		ByteArrayOutputStream bytes = new ByteArrayOutputStream();
		BinaryOutputStream output = new BinaryOutputStream(bytes);
		//
		output.write_uv(stringCache.get(td.getName()));
		output.write_uv(td.getBody().getIndex());
		writeSyntaxTree(td.getTree(),output);
		//
		output.close();
		return bytes.toByteArray();
	}

	/**
	 * Write a syntax tree to the output stream. The format
	 * of a syntax tree is one of the following:
	 *
	 * <pre>
	 * +-------------------+
	 * | uv : nLocs        |
	 * +-------------------+
	 * | Locations[nLocs]  |
	 * +-------------------+
	 * </pre>
	 *
	 *
	 *
	 * @param register
	 *            Register to be written out
	 * @param output
	 * @throws
	 */
	private void writeSyntaxTree(SyntaxTree tree, BinaryOutputStream output) throws IOException {
		List<wycs.lang.SyntaxTree.Location<?>> locations = tree.getLocations();
		output.write_uv(locations.size());
		for(int i=0;i!=locations.size();++i) {
			Location<?> location = locations.get(i);
			writeLocation(location,output);
		}
	}

	/**
	 * Write details of a Location to the output stream. The format
	 * of a location is:
	 *
	 * <pre>
	 * +-------------------+
	 * | uv : nTypes       |
	 * +-------------------+
	 * | uv[] : typeIdxs   |
	 * +-------------------+
	 * | uv : nAttrs       |
	 * +-------------------+
	 * | Bytecode          |
	 * +-------------------+
	 * | Attribute[nAttrs] |
	 * +-------------------+
	 * </pre>
	 *
	 */
	private void writeLocation(SyntaxTree.Location<?> location, BinaryOutputStream output) throws IOException {
		output.write_uv(typeCache.get(location.getType()));
		output.write_uv(0); // no attributes for now
		writeBytecode(location.getCode(), output);
	}

	/**
	 * <p>
	 * Write out a given bytecode whose format is currently given as follows:
	 * </p>
	 *
	 * <pre>
	 * +-------------------+
	 * | u8 : opcode       |
	 * +-------------------+
	 * | uv : nAttrs       |
	 * +-------------------+
	 * | Attribute[nAttrs] |
	 * +-------------------+
	 *        ...
	 *
	 * </pre>
	 *
	 * <p>
	 * <b>NOTE:</b> The intention is to support a range of different bytecode
	 * formats in order to optimise the common cases. For example, when there
	 * are no targets, no operands, no types, etc. Furthermore, when the size of
	 * items can be reduced from uv to u4, etc.
	 * </p>
	 */
	private void writeBytecode(Bytecode code, BinaryOutputStream output)
			throws IOException {
		output.write_u8(code.getOpcode().ordinal());
		writeOperands(code,output);
		if (code instanceof Bytecode.Stmt) {
			writeBlocks((Bytecode.Stmt) code, output);
		}
		writeExtras(code, output);
	}

	private void writeOperands(Bytecode code, BinaryOutputStream output) throws IOException {
		Bytecode.Schema schema = AbstractBytecode.schemas[code.getOpcode().ordinal()];
		switch(schema.getOperands()) {
		case ZERO:
			// do nout
			break;
		case ONE:
			output.write_uv(code.getOperand(0));
			break;
		case TWO:
			output.write_uv(code.getOperand(0));
			output.write_uv(code.getOperand(1));
			break;
		case MANY:
			writeUnboundArray(code.getOperands(),output);
		}
	}

	private void writeBlocks(Bytecode.Stmt code, BinaryOutputStream output) throws IOException {
		Bytecode.Schema schema = AbstractBytecode.schemas[code.getOpcode().ordinal()];
		switch(schema.getBlocks()) {
		case ZERO:
			// do nout
			break;
		case ONE:
			output.write_uv(code.getBlock(0));
			break;
		case TWO:
			output.write_uv(code.getBlock(0));
			output.write_uv(code.getBlock(1));
			break;
		case MANY:
			writeUnboundArray(code.getBlocks(),output);
		}
	}
	private void writeUnboundArray(int[] values, BinaryOutputStream output) throws IOException {
		output.write_uv(values.length);
		// Write operand locations
		for (int i = 0; i != values.length; ++i) {
			output.write_uv(values[i]);
		}
	}

	/**
	 * Write the "rest" of a bytecode instruction. This includes additional
	 * information as specified for the given opcode. For compound bytecodes,
	 * this includes the block identifier(s) of the nested block(s) in question.
	 * For branching bytecodes, it will include the branch destination as a
	 * relative offset. Other bytecodes include indices which identify constants
	 * in one of the pools.
	 *
	 * @param code
	 *            --- The bytecode to be written.
	 * @param offset
	 *            --- The current offset of this bytecode in the bytecode array
	 *            being generated. This offset is measured in complete
	 *            bytecodes, not in e.g. bytes. Therefore, the first bytecode
	 *            has offset zero, the second bytecode has offset 1, etc. The
	 *            offset is required for calculating jump targets for branching
	 *            instructions (e.g. goto). Since jump targets (in short form)
	 *            are encoded as a relative offset, we need to know our current
	 *            offset to compute the relative target.
	 * @param output
	 *            --- The binary output stream to which this bytecode is being
	 *            written.
	 * @throws IOException
	 */
	private void writeExtras(Bytecode code, BinaryOutputStream output) throws IOException {
		//
		switch (code.getOpcode()) {
		case CONST: {
			Bytecode.Constant c = (Bytecode.Constant) code;
			output.write_uv(constantCache.get(c.getValue()));
			break;
		}
		case VARDECL: {
			Bytecode.VariableDeclaration d = (Bytecode.VariableDeclaration) code;
			output.write_uv(stringCache.get(d.getName()));
			break;
		}
		}
	}

	/**
	 * Build the various pools of items (strings, types, constants, etc) which
	 * are used within the bytecodes, and within the declarations (e.g.
	 * assertions, etc). Each pool consists of an array of indexed items of the
	 * same kind. Items in some pools (e.g. constant) may refer to items in
	 * other pools (e.g. string) and this referencing is done via an index into
	 * the given pool.
	 *
	 * @param module
	 */
	private void buildPools(WycsFile module) {
		stringPool.clear();
		stringCache.clear();

		pathPool.clear();
		pathCache.clear();
		// preload the path root
		pathPool.add(null);
		pathCache.put(wyfs.util.Trie.ROOT,0);

		constantPool.clear();
		constantCache.clear();

		typePool.clear();
		typeCache.clear();

		addPathItem(module.getEntry().id());
		for(WycsFile.Declaration d : module.getDeclarations()) {
			buildPools(d);
		}
	}

	private void buildPools(WycsFile.Declaration declaration) {
		if(declaration instanceof WycsFile.Macro) {
			buildPools((WycsFile.Macro)declaration);
		} else if(declaration instanceof WycsFile.Type) {
			buildPools((WycsFile.Type)declaration);
		} else if(declaration instanceof WycsFile.Function) {
			buildPools((WycsFile.Function)declaration);
		} else if(declaration instanceof WycsFile.Assert) {
			buildPools((WycsFile.Assert)declaration);
		}
	}

	private void buildPools(WycsFile.Macro declaration) {
		addStringItem(declaration.getName());
		addTypeItem(declaration.getType());
		buildPools(declaration.getTree());
	}

	private void buildPools(WycsFile.Type declaration) {
		addStringItem(declaration.getName());
		addTypeItem(declaration.getType());
		buildPools(declaration.getTree());
	}

	private void buildPools(WycsFile.Function declaration) {
		addStringItem(declaration.getName());
		addTypeItem(declaration.getType());
	}

	private void buildPools(WycsFile.Assert declaration) {
		addStringItem(declaration.getName());
		buildPools(declaration.getTree());
	}


	private void buildPools(SyntaxTree tree) {
		for(Location<?> e : tree.getLocations()) {
			buildPools(e);
		}
	}

	private void buildPools(SyntaxTree.Location<?> loc) {
		addTypeItem(loc.getType());
		buildPools(loc.getCode());
	}


	private void buildPools(Bytecode code) {

		// First, deal with special cases
		if(code instanceof Bytecode.Constant) {
			Bytecode.Constant c = (Bytecode.Constant) code;
			addConstantItem(c.getValue());
		} else if(code instanceof Bytecode.Cast) {
			Bytecode.Cast c = (Bytecode.Cast) code;
			addTypeItem(c.getTarget());
		}
	}


	private int addNameItem(NameID name) {
		Integer index = nameCache.get(name);
		if(index == null) {
			int i = namePool.size();
			nameCache.put(name, i);
			namePool.add(new NAME_Item(addPathItem(name.module()),
					addStringItem(name.name())));
			return i;
		} else {
			return index;
		}
	}

	private int addStringItem(String string) {
		Integer index = stringCache.get(string);
		if(index == null) {
			int i = stringPool.size();
			stringCache.put(string, i);
			stringPool.add(string);
			return i;
		} else {
			return index;
		}
	}

	private int addPathItem(Path.ID pid) {
		Integer index = pathCache.get(pid);
		if(index == null) {
			int parent = addPathItem(pid.parent());
			int i = pathPool.size();
			pathPool.add(new PATH_Item(parent,addStringItem(pid.last())));
			pathCache.put(pid, i);
			return i;
		} else {
			return index;
		}
	}

	private int addTypeItem(SemanticType t) {

		// TODO: this could be made way more efficient. In particular, we should
		// combine resources into a proper aliased pool rather than write out
		// types individually ... because that's sooooo inefficient!

		Integer index = typeCache.get(t);
		if(index == null) {
			int i = typePool.size();
			typeCache.put(t, i);
			typePool.add(t);
			return i;
		} else {
			return index;
		}
	}

	private int addConstantItem(Value v) {

		Integer index = constantCache.get(v);
		if(index == null) {
			// All subitems must have lower indices than the containing item.
			// So, we must add subitems first before attempting to allocate a
			// place for this value.
			addConstantSubitems(v);

			// finally allocate space for this constant.
			int i = constantPool.size();
			constantCache.put(v, i);
			constantPool.add(v);
			return i;
		}
		return index;
	}

	private void addConstantSubitems(Value v) {
		if(v instanceof Value.String) {
			Value.String s = (Value.String) v;
			addStringItem(s.value);
		} else if(v instanceof Value.Array) {
			Value.Array s = (Value.Array) v;
			for (Value e : s.values) {
				addConstantItem(e);
			}
		} else if(v instanceof Value.Tuple) {
			Value.Tuple t = (Value.Tuple) v;
			for (Value e : t.values) {
				addConstantItem(e);
			}
		}
	}

	/**
	 * An PATH_Item represents a path item.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class PATH_Item {
		/**
		 * The index in the path pool of the parent for this item, or -1 if it
		 * has not parent.
		 */
		public final int parentIndex;

		/**
		 * The index of this path component in the string pool
		 */
		public final int stringIndex;

		public PATH_Item(int parentIndex, int stringIndex) {
			this.parentIndex = parentIndex;
			this.stringIndex = stringIndex;
		}
	}
	private enum NAME_Kind {
		PACKAGE(0),
		MODULE(1),
		CONSTANT(2),
		TYPE(3),
		FUNCTION(4),
		METHOD(5);

		private final int kind;

		private NAME_Kind(int kind) {
			this.kind = kind;
		}

		public int kind() {
			return kind;
		}
	}

	/**
	 * A NAME_Item represents a named path item, such as a package, module or
	 * something within a module (e.g. a function or method declaration).
	 *
	 * @author David J. Pearce
	 *
	 */
	private class NAME_Item {
		/**
		 * The kind of name item this represents.
		 */
		// public final NAME_Kind kind;

		/**
		 * Index of path for this item in path pool
		 */
		public final int pathIndex;

		/**
		 * Index of string for this named item
		 */
		public final int nameIndex;

		public NAME_Item(/*NAME_Kind kind, */int pathIndex, int nameIndex) {
			//this.kind = kind;
			this.pathIndex = pathIndex;
			this.nameIndex = nameIndex;
		}
	}

	// =========================================================================
	// BLOCK identifiers
	// =========================================================================

	public final static int BLOCK_Header = 0;
	public final static int BLOCK_Module = 1;
	public final static int BLOCK_Documentation = 2;
	public final static int BLOCK_License = 3;
	// ... (anticipating some others here)
	public final static int BLOCK_Macro = 11;
	public final static int BLOCK_Function = 12;
	public final static int BLOCK_Assert = 13;
	public final static int BLOCK_Type = 14;
	// ... (anticipating some others here)

	// =========================================================================
	// CONSTANT identifiers
	// =========================================================================

	public final static int CONSTANT_Null = 0;
	public final static int CONSTANT_True = 1;
	public final static int CONSTANT_False = 2;
	public final static int CONSTANT_Int = 3;
	public final static int CONSTANT_Real = 4;
	public final static int CONSTANT_Array = 5;
	public final static int CONSTANT_String = 6;
	public final static int CONSTANT_Tuple = 7;
}
