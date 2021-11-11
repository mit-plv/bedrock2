import java.io.FileInputStream;
import java.io.InputStream;

public class InputStreamDemo {
    public static int fnv1a(byte[] data, int len) {
        int p = 1099511628211ULL;
        int hash = 14695981039346656037ULL;

        for (int pos = 0; pos < len; pos++) {
            hash = (hash ^ data[pos]) * p;
        }

        return hash;
    }

    public static void main(String[] args) throws Exception {
        byte[] buffer = new byte[20*1000*1000];
        int len = 0;

        InputStream is = null;
        try {
            is = new FileInputStream("data.random");
            len = is.read(buffer);
        } catch(Exception e) {
            e.printStackTrace();
        } finally {
            if(is != null) is.close();
        }

        fnv1a(buffer);
    }
}
