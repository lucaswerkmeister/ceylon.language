package ceylon.language;

import com.redhat.ceylon.compiler.java.metadata.Ceylon;
import com.redhat.ceylon.compiler.java.metadata.Ignore;
import com.redhat.ceylon.compiler.java.metadata.Name;
import com.redhat.ceylon.compiler.java.metadata.Sequenced;
import com.redhat.ceylon.compiler.java.metadata.TypeInfo;
import com.redhat.ceylon.compiler.java.metadata.TypeParameter;
import com.redhat.ceylon.compiler.java.metadata.TypeParameters;
import com.redhat.ceylon.compiler.java.metadata.Variance;

@Ceylon
@TypeParameters({
    @TypeParameter(value = "Key", variance = Variance.IN,
            satisfies="ceylon.language.Equality"),
    @TypeParameter(value = "Item", variance = Variance.OUT)
})
public interface Correspondence<Key,Item> {
    
    @TypeInfo("Item|ceylon.language.Nothing")
    public Item item(@Name("key") Key key);

    public boolean defines(@Name("key") Key key);

    public Category getKeys();

    public boolean definesEvery(@Sequenced @Name("keys") 
    @TypeInfo("ceylon.language.Empty|ceylon.language.Sequence<Key>")
    Iterable<? extends Key> keys);

    public boolean definesAny(@Sequenced @Name("keys") 
    @TypeInfo("ceylon.language.Empty|ceylon.language.Sequence<Key>")
    Iterable<? extends Key> keys);

    @TypeInfo("ceylon.language.Empty|ceylon.language.Sequence<Item|ceylon.language.Nothing>")
    public Iterable<? extends Item> items(@Sequenced @Name("keys") 
    @TypeInfo("ceylon.language.Empty|ceylon.language.Sequence<Key>")
    Iterable<? extends Key> keys);

    @Ignore
    class Items<Key,Item>
            implements Sequence<Item> {
        private Sequence<? extends Key> keys;
        private Correspondence<Key, Item> $this;
        Items(Correspondence<Key,Item> $this, Sequence<? extends Key> keys){
            this.keys = keys;
            this.$this = $this;
        }
        public final long getLastIndex() {
            return keys.getLastIndex();
        }
        public final Item getFirst() {
            return $this.item(keys.getFirst());
        }
        public final Iterable<? extends Item> getRest() {
            return $this.items(keys.getRest());
        }
        public final Item item(Integer index) {
            Key key = keys.item(index);
            if (key != null) {
                return $this.item(key);
            }
            else {
                return null;
            }
        }
        @Override
        public java.lang.String toString() {
            return Sequence$impl.toString(this);		
        }
        public final Sequence<Item> getClone() {
            return this;
        }
        @Override
        public Category getKeys() {
            return Correspondence$impl.getKeys(this);
        }
        @Override
        public boolean definesEvery(Iterable<? extends Integer> keys) {
            return Correspondence$impl.definesEvery(this, keys);
        }
        @Override
        public boolean definesAny(Iterable<? extends Integer> keys) {
            return Correspondence$impl.definesAny(this, keys);
        }
        @Override
        public Iterable<? extends Item> items(Iterable<? extends Integer> keys) {
            return Correspondence$impl.items(this, keys);
        }
        @Override
        public boolean getEmpty() {
            return Sequence$impl.getEmpty(this);
        }
        @Override
        public long getSize() {
            return Sequence$impl.getSize(this);
        }
        @Override
        public Item getLast() {
            return Sequence$impl.getLast(this);
        }
        @Override
        public boolean defines(Integer index) {
            return Sequence$impl.defines(this, index);
        }
        @Override
        public Iterator<? extends Item> getIterator() {
            return Sequence$impl.getIterator(this);
        }
        @Override
        public Iterable<? extends Item> segment(Integer from, Integer length) {
        	Iterable<? extends Key> keys = this.keys.segment(from, length);
        	if (keys.getEmpty()) {
        		return $empty.getEmpty();
        	}
        	else {
        		return new Items<Key,Item>($this, (Sequence<? extends Key>)keys);
        	}
        }
        @Override
        public Iterable<? extends Item> span(Integer from, Integer to) {
        	Iterable<? extends Key> keys = this.keys.span(from, to);
        	if (keys.getEmpty()) {
        		return $empty.getEmpty();
        	}
        	else {
        		return new Items<Key,Item>($this, (Sequence<? extends Key>)keys);
        	}
        }
    }
    
    @Ignore
    public static final class Correspondence$impl {

        public static <Key,Item> boolean defines(Correspondence<Key,Item> $this, Key key){
            return $this.item(key) != null;
        }

        public static <Key,Item> Category getKeys(final Correspondence<Key,Item> $this){
            Category keys = new Category() {
                public boolean contains(java.lang.Object value) {
                    // FIXME
                    if (true/*value instanceof Key*/) {
                        return $this.defines((Key)value);
                    }
                    else {
                        return false;
                    }
                }

                @Override
                public boolean containsEvery(ceylon.language.Iterable<?> elements) {
                    return Category$impl.containsEvery(this, elements);
                }

                @Override
                public boolean containsAny(ceylon.language.Iterable<?> elements) {
                    return Category$impl.containsAny(this, elements);
                }
            };
            return keys;
        }

        public static <Key,Item> boolean definesEvery(Correspondence<Key,Item> $this, ceylon.language.Iterable<? extends Key> keys){
            for (ceylon.language.Iterator<? extends Key> $key$iter$0 = keys.getIterator(); $key$iter$0 != null; $key$iter$0 = $key$iter$0.getTail()) {
                final Key key = $key$iter$0.getHead();
                if (!$this.defines(key)) {
                    return false;
                }
            }
            return true;
        }

        public static <Key,Item> boolean definesAny(Correspondence<Key,Item> $this, ceylon.language.Iterable<? extends Key> keys) {
            for (ceylon.language.Iterator<? extends Key> $key$iter$0 = keys.getIterator(); $key$iter$0 != null; $key$iter$0 = $key$iter$0.getTail()) {
                final Key key = $key$iter$0.getHead();
                if ($this.defines(key)) {
                    return true;
                }
            }
            return false;
        }

        public static <Key,Item> Iterable<? extends Item> items(Correspondence<Key,Item> $this, ceylon.language.Iterable<? extends Key> keys) {
            if (keys instanceof Sequence) {
                final ceylon.language.Sequence<? extends Key> $keys$1 = (ceylon.language.Sequence<? extends Key>)keys;
                return new Correspondence.Items($this, $keys$1.getClone());
            }
            else {
                return $empty.getEmpty();
            }
        }
    }
}
