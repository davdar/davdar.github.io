import java.util.*;

public class ListMap {
  public interface Fun<A,B> {
    public B call(A x);
  }

  // listMap : ('a -> 'b) * 'a list -> 'b list
  public static <A,B> List<B> listMap(Fun<A,B> f, List<A> xs) {
    ArrayList<B> ys = new ArrayList<B>();
    for (int i = 0 ; i < xs.size() ; i++) {
      ys.add(f.call(xs.get(i)));
    }
    return ys;
  }

  public static void main(String[] args) {
    ArrayList<Integer> xs = new ArrayList<Integer>(Arrays.asList(1,2,3,4,5));
    Fun<Integer,Integer> f = new Fun<Integer,Integer>() {
      public Integer call(Integer x) { return x + 1; }
    };
    List<Integer> ys = listMap(f,xs);
    System.out.println(ys);

    Object zs = ys;
    System.out.println(zs.toString());
    // if (zs instanceof ArrayList) {
    //   ArrayList<Integer> other_ys = (ArrayList) zs;
    // }
  }
}
