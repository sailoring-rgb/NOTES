class Contact {
    private final String name;
    private final int age;
    private final long phoneNumber;
    private final String company;
    private final List<String> emails;

    public Contact (String name, int age, long phoneNumber, String company, List<String> emails){
        this.name = name;
        this.age = age;
        this.phoneNumber = phoneNumber;
        this.company = company;
        this.emails = new ArrayList<>(emails);
    }

    public String getName(){
        return this.name;
    }
    
    public void serialize (DataOutputStream out) throws IOException {
        out.writeUTF(this.name);
        out.writeInt(this.age);
        out.writeLong(this.phoneNumber);

        // company field
        if(this.company == null){
            out.writeBoolean(false);
        } else {
            out.writeBoolean(true);
            out.writeUTF(this.company);
        }
        out.writeInt(this.emails.size());
        for(String s: this.emails) {
            out.writeUTF(s);
        }
    }

    public static Contact deserialize (DataInputStream in) throws IOException{
        String name = in.readUTF();
        int age = in.readInt();
        long phoneNumber = in.readLong();
        
        String company = null;
        if(in.readBoolean())
            company = in.readUTF();
        
        List<String> emails = new ArrayList<>();
        int emaillistSize = in.readInt();
        for(int i = 0; i < emaillistSize; i++)
            emails.add(in.readUTF());
        
        return new Contact (name, age, phoneNumber, company, emails);
    }

    public String toString(){
        StringBuilder builder = new StringBuilder();
        builder.append(this.name).append(";");
        builder.append(this.age).append(";");
        builder.append(this.phoneNumber).append(";");
        builder.append(this.company).append(";");
        builder.append("{");
        for(String s: this.emails){
            builder.append(s).append(";");
        }
        builder.append("}");
        return builder.toString();
    }
}