package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Comparator;

import wyal.lang.Domain;
import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;

/**
 * The small world domain stems from the theory that all bugs can be found with
 * a "small world".
 *
 * @author David J. Pearce
 *
 */
public class SmallWorldDomain implements Domain {
	private final int intLowerBound = -5;
	private final int intUpperBound = 5;
	private final int arrayLengthBound = 2;
	private final int depthBound = 2;
	protected final NameResolver resolver;

	public SmallWorldDomain(NameResolver resolver) {
		this.resolver = resolver;
	}

	@Override
	public Generator generator(Type type) {
		return generator(type,0);
	}

	public Generator generator(Type type, int depth) {
		if(depth >= depthBound) {
			return null;
		} else if (type instanceof Type.Null) {
			return new NullGenerator();
		} else if (type instanceof Type.Bool) {
			return new BoolGenerator();
		} else if (type instanceof Type.Int) {
			return new IntGenerator(intLowerBound, intUpperBound);
		} else if (type instanceof Type.Record) {
			Type.Record record = (Type.Record) type;
			FieldDeclaration[] fields = record.getFields();
			Arrays.sort(fields,fieldComparator);
			Identifier[] fieldNames = new Identifier[fields.length];
			Domain.Generator[] generators = new Domain.Generator[fields.length];
			for (int i = 0; i != generators.length; ++i) {
				FieldDeclaration field = fields[i];
				fieldNames[i] = field.getVariableName();
				generators[i] = generator(field.getType(),depth);
			}
			return new RecordGenerator(fieldNames,generators);
		} else if (type instanceof Type.Array) {
			Type elementType = ((Type.Array) type).getElement();
			Domain.Generator[] generators = new Domain.Generator[arrayLengthBound];
			for (int i = 0; i != generators.length; ++i) {
				generators[i] = generator(elementType,depth);
			}
			return new ArrayGenerator(generators);
		} else if (type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			Domain.Generator[] generators = new Domain.Generator[arrayLengthBound];
			for (int i = 0; i != generators.length; ++i) {
				generators[i] = generator(union.getOperand(i),depth);
			}
			return new UnionGenerator(generators);
		} else if(type instanceof Type.Nominal) {
			Type.Nominal nominal = (Type.Nominal) type;
			try {
				Named.Type decl = resolver.resolveExactly(nominal.getName(), Named.Type.class);
				// FIXME: what about recursive types?
				return generator(decl.getVariableDeclaration().getType(),depth+1);
			} catch (ResolutionError e) {
				throw new RuntimeException(e);
			}
		} else {
			throw new IllegalArgumentException("unknown type encountered: " + type);
		}
	}

	private static final Comparator<FieldDeclaration> fieldComparator = new Comparator<FieldDeclaration>() {

		@Override
		public int compare(FieldDeclaration o1, FieldDeclaration o2) {
			return o1.getVariableName().compareTo(o2.getVariableName());
		}

	};

	private static class NullGenerator implements Domain.Generator {

		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public Object get() {
			return null;
		}

		@Override
		public void next() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void reset() {}
	}

	private static class BoolGenerator implements Domain.Generator {
		private int count;

		@Override
		public boolean hasNext() {
			return count <= 1;
		}

		@Override
		public Object get() {
			if(count == 0) {
				return false;
			} else {
				return true;
			}
		}

		@Override
		public void next() {
			count = count + 1;
		}

		@Override
		public void reset() {
			count = 0;
		}

	}

	private static class IntGenerator implements Domain.Generator {
		private final int max;
		private final int upperBound;
		private int count;

		public IntGenerator(int lowerBound, int upperBound) {
			this.max = upperBound - lowerBound;
			this.upperBound = upperBound;
			this.count = 0;
		}

		@Override
		public boolean hasNext() {
			return count <= max;
		}

		@Override
		public Object get() {
			int val = count <= upperBound ? count : -(count-upperBound);
			return BigInteger.valueOf(val);
		}

		@Override
		public void next() {
			count = count + 1;
		}

		@Override
		public void reset() {
			count = 0;
		}

	}

	private static class ArrayGenerator implements Domain.Generator {
		private final Domain.Generator[] generators;
		private int length;

		public ArrayGenerator(Domain.Generator[] generators) {
			this.generators = generators;
			this.length = 0;
		}

		@Override
		public boolean hasNext() {
			return length < generators.length;
		}

		@Override
		public Object get() {
			Object[] array = new Object[length];
			for(int i=0;i!=length;++i) {
				array[i] = generators[i].get();
			}
			return array;
		}

		@Override
		public void next() {
			for(int i=0;i!=length;++i) {
				Domain.Generator gen = generators[i];
				if(gen.hasNext()) {
					gen.next();
					return;
				} else {
					gen.reset();
				}
			}
			// If we get here then we have exhausted all arrays upto the given
			// length.
			length = length + 1;
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
			this.length = 0;
		}

	}

	private static class RecordGenerator implements Domain.Generator {
		private final Identifier[] fields;
		private final Domain.Generator[] generators;


		public RecordGenerator(Identifier[] fields, Domain.Generator[] generators) {
			this.fields = fields;
			this.generators = generators;
		}

		@Override
		public boolean hasNext() {
			for(int i=0;i!=generators.length;++i) {
				if(generators[i].hasNext()) {
					return true;
				}
			}
			return false;
		}

		@Override
		public Object get() {
			Object[] array = new Object[generators.length];
			for(int i=0;i!=generators.length;++i) {
				array[i] = generators[i].get();
			}
			return new Interpreter.Record(fields,array);
		}

		@Override
		public void next() {
			for (int i = 0; i != generators.length; ++i) {
				Domain.Generator gen = generators[i];
				if (gen.hasNext()) {
					gen.next();
					return;
				} else {
					gen.reset();
				}
			}
			// If we get here then we have exhausted all arrays upto the given
			// length.
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
		}

	}


	private static class UnionGenerator implements Domain.Generator {
		private final Domain.Generator[] generators;
		private int index;

		public UnionGenerator(Domain.Generator[] generators) {
			this.generators = generators;
			this.index = 0;
		}

		@Override
		public boolean hasNext() {
			return index < generators.length;
		}

		@Override
		public Object get() {
			return generators[index].get();
		}

		@Override
		public void next() {
			while(!generators[index].hasNext()) {
				index = index + 1;
			}
			generators[index].next();
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
			this.index = 0;
		}

	}
}
