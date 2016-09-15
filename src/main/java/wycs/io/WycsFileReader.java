package wycs.io;

import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import wycc.util.Pair;
import wyautl.core.Automaton;
import wyautl.io.BinaryAutomataReader;
import wybs.lang.Attribute;
import wybs.lang.NameID;
import wycs.lang.*;
import wycs.util.AbstractBytecode;
import wyfs.io.BinaryInputStream;
import wyfs.lang.Path;
import wyfs.util.Trie;


public class WycsFileReader {
	private static final char[] magic = { 'W', 'Y', 'C', 'S', 'F', 'I', 'L',
			'E' };

	private Path.Entry<WycsFile> entry;
	private BinaryInputStream input;
	private String[] stringPool;
	private Path.ID[] pathPool;
	private NameID[] namePool;
	private Value[] constantPool;
	private SemanticType[] typePool;

	public WycsFileReader(Path.Entry<WycsFile> entry, InputStream input) {
		this.entry = entry;
		this.input = new BinaryInputStream(input);
	}

	public void close() throws IOException {
		input.close();
	}

	public WycsFile read() throws IOException {
		for (int i = 0; i != 8; ++i) {
			char c = (char) input.read_u8();
			if (magic[i] != c) {
				throw new IllegalArgumentException("invalid magic number");
			}
		}

		// header block
		int kind = input.read_uv();
		int size = input.read_uv();
		input.pad_u8();

		if (kind != WycsFileWriter.BLOCK_Header) {
			throw new IllegalArgumentException("header block must come first");
		}

		int majorVersion = input.read_uv();
		int minorVersion = input.read_uv();

		int stringPoolSize = input.read_uv();
		int pathPoolSize = input.read_uv();
		int namePoolSize = input.read_uv();
		int typePoolSize = input.read_uv();
		int constantPoolSize = input.read_uv();

		int numBlocks = input.read_uv();

		readStringPool(stringPoolSize);
		readPathPool(pathPoolSize);
		readNamePool(namePoolSize);
		readTypePool(typePoolSize);

		readConstantPool(constantPoolSize);

		input.pad_u8();

		return readModule();
	}

	private void readStringPool(int size) throws IOException {
		final String[] myStringPool = new String[size];

		for (int i = 0; i != size; ++i) {
			int length = input.read_uv();
			try {
				byte[] data = new byte[length];
				input.read(data);
				String str = new String(data, 0, length, "UTF-8");
				myStringPool[i] = str;
			} catch (UnsupportedEncodingException e) {
				throw new RuntimeException("UTF-8 Charset not supported?");
			}
		}
		stringPool = myStringPool;
	}

	private void readPathPool(int size) throws IOException {
		final Path.ID[] myPathPool = new Path.ID[size];
		myPathPool[0] = Trie.ROOT;

		for (int i = 1; i != size; ++i) {
			int parent = input.read_uv();
			int stringIndex = input.read_uv();
			Path.ID id;
			id = myPathPool[parent];
			id = id.append(stringPool[stringIndex]);
			myPathPool[i] = id;
		}
		pathPool = myPathPool;
	}

	private void readNamePool(int size) throws IOException {
		final NameID[] myNamePool = new NameID[size];

		for (int i = 0; i != size; ++i) {
			// int kind = input.read_uv();
			int pathIndex = input.read_uv();
			int nameIndex = input.read_uv();
			Path.ID id = pathPool[pathIndex];
			String name = stringPool[nameIndex];
			myNamePool[i] = new NameID(id, name);
		}

		namePool = myNamePool;
	}

	private void readConstantPool(int size) throws IOException {
		final Value[] myConstantPool = new Value[size];

		for (int i = 0; i != size; ++i) {
			int code = input.read_uv();
			Value constant;
			switch (code) {
			case WycsFileWriter.CONSTANT_Null:
				constant = Value.Null;
				break;
			case WycsFileWriter.CONSTANT_False:
				constant = Value.Bool(false);
				break;
			case WycsFileWriter.CONSTANT_True:
				constant = Value.Bool(true);
				break;
			case WycsFileWriter.CONSTANT_Int: {
				int len = input.read_uv();
				byte[] bytes = new byte[len];
				input.read(bytes);
				BigInteger bi = new BigInteger(bytes);
				constant = Value.Integer(bi);
				break;
			}
			case WycsFileWriter.CONSTANT_Real: {
				int len = input.read_uv();
				byte[] bytes = new byte[len];
				input.read(bytes);
				BigInteger mantissa = new BigInteger(bytes);
				int exponent = input.read_uv();
				constant = Value.Decimal(new BigDecimal(mantissa, exponent));
				break;
			}
			case WycsFileWriter.CONSTANT_String: {
				int index = input.read_uv();
				constant = Value.String(stringPool[index]);
				break;
			}
			case WycsFileWriter.CONSTANT_Array: {
				int len = input.read_uv();
				ArrayList<Value> values = new ArrayList<Value>();
				for (int j = 0; j != len; ++j) {
					int index = input.read_uv();
					values.add(myConstantPool[index]);
				}
				constant = Value.Array(values);
				break;
			}
			case WycsFileWriter.CONSTANT_Tuple: {
				int len = input.read_uv();
				ArrayList<Value> values = new ArrayList<Value>();
				for (int j = 0; j != len; ++j) {
					int index = input.read_uv();
					values.add(myConstantPool[index]);
				}
				constant = Value.Tuple(values);
				break;
			}
			default:
				throw new RuntimeException("Unknown constant encountered: "
						+ code);
			}
			myConstantPool[i] = constant;
		}

		constantPool = myConstantPool;
	}

	private void readTypePool(int size) throws IOException {
		final SemanticType[] myTypePool = new SemanticType[size];
		BinaryAutomataReader reader = new BinaryAutomataReader(input,
				Types.SCHEMA);
		Automaton global = reader.read();

		for (int i = 0; i != size; ++i) {
			Automaton automaton = new Automaton();
			int root = automaton.addAll(global.getRoot(i), global);
			automaton.setRoot(0, root);
			SemanticType t = SemanticType.construct(automaton);
			myTypePool[i] = t;
		}

		typePool = myTypePool;
	}

	private WycsFile readModule() throws IOException {
		int kind = input.read_uv(); // block identifier
		int size = input.read_uv();
		input.pad_u8();

		int pathIdx = input.read_uv();
		int numBlocks = input.read_uv();

		WycsFile wycsFile = new WycsFile(entry);

		List<WycsFile.Declaration> declarations = wycsFile.getDeclarations();
		for (int i = 0; i != numBlocks; ++i) {
			declarations.add(readBlock(wycsFile,WycsFile.Declaration.class));
		}

		Path.ID id = pathPool[pathIdx];

		return wycsFile;
	}

	private <T> T readBlock(WycsFile parent, Class<T> expected) throws IOException {

		input.pad_u8(); // pad out to next byte boundary

		int kind = input.read_uv();
		int size = input.read_uv();

		input.pad_u8(); // pad out to next byte boundary
		Object block;

		switch (kind) {
		case WycsFileWriter.BLOCK_Macro:
			block = readMacroBlockBody(parent);
			break;
		case WycsFileWriter.BLOCK_Type:
			block = readTypeBlockBody(parent);
			break;
		case WycsFileWriter.BLOCK_Function:
			block = readFunctionBlockBody(parent);
			break;
		case WycsFileWriter.BLOCK_Assert:
			block = readAssertBlockBody(parent);
			break;
		default:
			throw new RuntimeException("unknown block encountered (" + kind
					+ ")");
		}

		input.pad_u8(); // pad out to next byte boundary

		if (expected.isInstance(block)) {
			return (T) block;
		} else {
			throw new RuntimeException("incorrect block encountered (" + kind
					+ ")");
		}
	}

	// ====================================================================
	// Block body readers
	// ====================================================================

	private WycsFile.Declaration readMacroBlockBody(WycsFile parent) throws IOException {
		int nameIdx = input.read_uv();
		int typeIdx = input.read_uv();
		int body = input.read_uv();
		// Create declaration
		WycsFile.Macro decl = new WycsFile.Macro(parent, stringPool[nameIdx],
				(SemanticType.Function) typePool[typeIdx]);
		// Read tree and construct locations
		SyntaxTree tree = readSyntaxTree(decl);
		decl.setBody(tree.getLocation(body));
		// Done
		return decl;
	}

	private WycsFile.Declaration readTypeBlockBody(WycsFile parent) throws IOException {
		int nameIdx = input.read_uv();
		int typeIdx = input.read_uv();
		int[] invariant = readUnboundArray();
		//
		WycsFile.Type decl = new WycsFile.Type(parent, stringPool[nameIdx], typePool[typeIdx]);
		SyntaxTree tree = readSyntaxTree(decl);
		//
		for(int i=0;i!=invariant.length;++i) {
			decl.getInvariant().add(tree.getLocation(invariant[i]));
		}
		//
		return decl;
	}

	private WycsFile.Declaration readFunctionBlockBody(WycsFile parent) throws IOException {
		int nameIdx = input.read_uv();
		int typeIdx = input.read_uv();
		return new WycsFile.Function(parent, stringPool[nameIdx], (SemanticType.Function) typePool[typeIdx]);
	}

	private WycsFile.Declaration readAssertBlockBody(WycsFile parent) throws IOException {
		int nameIdx = input.read_uv();
		int body = input.read_uv();
		WycsFile.Assert decl =  new WycsFile.Assert(parent, stringPool[nameIdx]);
		// Read tree and construct locations
		SyntaxTree tree = readSyntaxTree(decl);
		decl.setBody(tree.getLocation(body));
		//
		return decl;
	}

	/**
	 * Read a syntax tree from the output stream. The format
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
	 * @param parent
	 * @return
	 * @throws IOException
	 */
	private SyntaxTree readSyntaxTree(WycsFile.Declaration parent) throws IOException {
		SyntaxTree tree = parent.getTree();
		int nLocs = input.read_uv();
		for(int i=0;i!=nLocs;++i) {
			tree.getLocations().add(readLocation(tree));
		}
		return tree;
	}

	/**
	 * Read details of a Location from the input stream. The format of a
	 * location is:
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
	 * @param output
	 * @throws IOException
	 */
	private SyntaxTree.Location<?> readLocation(SyntaxTree tree) throws IOException {
		int typeIdx = input.read_uv();
		SemanticType type = typePool[typeIdx];
		int nAttrs = input.read_uv();
		Bytecode bytecode = readBytecode();
		//
		List<Attribute> attributes = new ArrayList<Attribute>();
		//
		return new SyntaxTree.Location<Bytecode>(tree, type, bytecode, attributes);
	}

	/**
	 * <p>
	 * REad a given bytecode whose format is currently given as follows:
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
	 * </pre>
	 *
	 * <p>
	 * <b>NOTE:</b> The intention is to support a range of different bytecode
	 * formats in order to optimise the common cases. For example, when there
	 * are no targets, no operands, no types, etc. Furthermore, when the size of
	 * items can be reduced from uv to u4, etc.
	 * </p>
	 */
	private Bytecode readBytecode() throws IOException {
		int opcode = input.read_u8();
		// FIXME: read attributes!
		Bytecode.Schema schema = AbstractBytecode.schemas[opcode];
		// First, read and validate all operands, groups and blocks
		int[] operands = readOperands(schema);
		int[] blocks = readBlocks(schema);
		// Second, read all extras
		Object[] extras = readExtras(schema);
		// Finally, create the bytecode
		return schema.construct(opcode, operands, blocks, extras);
	}

	private int[] readOperands(Bytecode.Schema schema) throws IOException {
		switch(schema.getOperands()) {
		case ZERO:
			// do nout
			return null;
		case ONE:
			int o = input.read_uv();
			return new int[] { o };
		case TWO:
			int o1 = input.read_uv();
			int o2 = input.read_uv();
			return new int[] { o1, o2 };
		case MANY:
		default:
			return readUnboundArray();
		}
	}

	private int[] readBlocks(Bytecode.Schema schema) throws IOException {
		switch(schema.getBlocks()) {
		case ZERO:
			// do nout
			return null;
		case ONE:
			int o = input.read_uv();
			return new int[] { o };
		case TWO:
			int o1 = input.read_uv();
			int o2 = input.read_uv();
			return new int[] { o1, o2 };
		case MANY:
		default:
			return readUnboundArray();
		}
	}

	/**
	 * Read the list of extra components defined by a given bytecode schema.
	 * Each extra is interpreted in a slightly different fashion.
	 *
	 * @param schema
	 * @param labels
	 * @return
	 * @throws IOException
	 */
	private Object[] readExtras(Bytecode.Schema schema)
			throws IOException {
		Bytecode.Extras[] extras = schema.extras();
		Object[] results = new Object[extras.length];
		for(int i=0;i!=extras.length;++i) {
			switch(extras[i]) {
			case CONSTANT: {
				int constIdx = input.read_uv();
				results[i] = constantPool[constIdx];
				break;
			}
			case STRING: {
				int stringIdx = input.read_uv();
				results[i] = stringPool[stringIdx];
				break;
			}
			case NAME: {
				int nameIdx = input.read_uv();
				results[i] = namePool[nameIdx];
				break;
			}
			case TYPE: {
				int typeIdx = input.read_uv();
				results[i] = typePool[typeIdx];
				break;
			}
			case STRING_ARRAY: {
				int nStrings = input.read_uv();
				String[] strings = new String[nStrings];
				for(int j=0;j!=nStrings;++j) {
					int stringIdx = input.read_uv();
					strings[j] = stringPool[stringIdx];
				}
				results[i] = strings;
				break;
			}
			default:
				throw new RuntimeException("unknown bytecode extra encountered: " + extras[i]);
			}
		}
		return results;
	}

	private int[] readUnboundArray() throws IOException {
		int size = input.read_uv();
		int[] array = new int[size];
		for(int i=0;i!=size;++i) {
			array[i] = input.read_uv();
		}
		return array;
	}

}
