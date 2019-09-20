

import java.io.Serializable;

public class ArgumentInfo implements Serializable {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private String type;
	private String name;
	
	public ArgumentInfo() {
		
	}
	
	public ArgumentInfo(String type, String name) {
		this.type = type;
		this.name = name;
	}
	
	public String getType() {
		return type;
	}
	public void setType(String type) {
		this.type = type;
	}
	public String getName() {
		return name;
	}
	public void setName(String name2) {
		this.name = name2;
	}
}